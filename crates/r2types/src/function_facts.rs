use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::callee::{CalleeIdentityContext, CalleeResolutionFacts, CallsiteKey};
use crate::context::{ExternalStackSlotRole, ExternalStackSlotSpec, StackSlotKey};
use crate::facts::{
    FunctionSignatureProjection, FunctionSignatureSpec, FunctionTypeFacts,
    OutParamCertificateEvidence, OutParamCertificateSource, SignatureCertificateSource,
    SignatureProjectionResult, VisibleBindingKind,
};
use crate::{CTypeLike, normalize_external_type_name, parse_c_type_like};

pub type OpSiteKey = (u64, usize);
pub type MemoryOpSiteKey = (u64, usize, bool);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ParamSlotResolver {
    slots_by_value: BTreeMap<r2ssa::ValueId, usize>,
}

impl ParamSlotResolver {
    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.slots_by_value.is_empty()
    }

    fn slot_for_value(&self, value: r2ssa::ValueId) -> Option<usize> {
        self.slots_by_value.get(&value).copied()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalysisPlans {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_build: Option<r2sym::ArtifactBuildPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub query: Option<r2sym::QueryPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_plan: Option<r2sym::TypePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub decompile: Option<r2sym::DecompilePlan>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionCallsiteFacts {
    pub by_callsite: BTreeMap<CallsiteKey, CallsiteArgumentFacts>,
}

impl FunctionCallsiteFacts {
    pub fn is_empty(&self) -> bool {
        self.by_callsite.is_empty()
    }

    pub fn arguments_for_site(&self, callsite: CallsiteKey) -> Option<&CallsiteArgumentFacts> {
        self.by_callsite.get(&callsite)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionCallResultFacts {
    pub by_value: BTreeMap<r2ssa::ValueId, CallResultFact>,
    pub by_callsite: BTreeMap<CallsiteKey, Vec<r2ssa::ValueId>>,
}

impl FunctionCallResultFacts {
    pub fn is_empty(&self) -> bool {
        self.by_value.is_empty() && self.by_callsite.is_empty()
    }

    pub fn result_for_value(&self, value: r2ssa::ValueId) -> Option<&CallResultFact> {
        self.by_value.get(&value)
    }

    pub fn results_for_site(&self, callsite: CallsiteKey) -> impl Iterator<Item = &CallResultFact> {
        self.by_callsite
            .get(&callsite)
            .into_iter()
            .flatten()
            .filter_map(|value| self.by_value.get(value))
    }

    /// The value the call boundary itself defines.
    ///
    /// A result may acquire a stable stack owner after copies, a store and a
    /// reload. That owner is useful for later reads, but it is not the value
    /// whose definition the call statement renders. The boundary definition is
    /// the earliest identity result carried in a register; propagated identity
    /// results occur later. A tie is ambiguous and therefore remains unowned.
    pub fn definition_for_site(&self, callsite: CallsiteKey) -> Option<&CallResultFact> {
        let is_boundary_definition = |result: &CallResultFact| {
            result.relation.is_identity()
                && matches!(result.carrier, r2ssa::ReturnCarrier::Register { .. })
        };
        let earliest = self
            .results_for_site(callsite)
            .filter(|result| is_boundary_definition(result))
            .map(|result| result.at)
            .min()?;
        let mut definitions = self
            .results_for_site(callsite)
            .filter(|result| is_boundary_definition(result) && result.at == earliest);
        let definition = definitions.next()?;
        definitions.next().is_none().then_some(definition)
    }

    pub fn owner_for_site(&self, callsite: CallsiteKey) -> Option<&r2ssa::ValueOwner> {
        let direct_stack_owner = self.unique_owner_for_site_matching(callsite, |result, owner| {
            result.relation.is_identity()
                && matches!(&result.carrier, r2ssa::ReturnCarrier::Register { .. })
                && matches!(owner, r2ssa::ValueOwner::StackSlot { .. })
        });
        match direct_stack_owner {
            Ok(Some(owner)) => return Some(owner),
            Err(()) => return None,
            Ok(None) => {}
        }

        let carrier_stack_owner = self.unique_owner_for_site_matching(callsite, |result, owner| {
            result.relation.is_identity()
                && matches!(
                (&result.carrier, owner),
                (
                    r2ssa::ReturnCarrier::StackSlot {
                        object: carrier_object,
                        offset: carrier_offset,
                        ..
                    },
                    r2ssa::ValueOwner::StackSlot {
                        object: owner_object,
                        offset: owner_offset,
                    }
                ) if carrier_object == owner_object && carrier_offset == owner_offset
                )
        });
        match carrier_stack_owner {
            Ok(Some(owner)) => return Some(owner),
            Err(()) => return None,
            Ok(None) => {}
        }

        // A result carried in a register and owned by a value. Every branch
        // above requires a stack slot, so a register-carried result never had
        // an owner and the call site was never recorded as assigning it.
        let register_owner = self.unique_owner_for_site_matching(callsite, |result, owner| {
            result.relation.is_identity()
                && matches!(&result.carrier, r2ssa::ReturnCarrier::Register { .. })
                && matches!(owner, r2ssa::ValueOwner::Value(_))
        });
        match register_owner {
            Ok(Some(owner)) => return Some(owner),
            Err(()) => return None,
            Ok(None) => {}
        }

        self.unique_owner_for_site_matching(callsite, |result, owner| {
            result.relation.is_identity() && matches!(owner, r2ssa::ValueOwner::StackSlot { .. })
        })
        .ok()
        .flatten()
    }

    pub fn owner_for_value(&self, value: r2ssa::ValueId) -> Option<&r2ssa::ValueOwner> {
        self.result_for_value(value)
            .and_then(|result| result.owner.as_ref())
    }

    fn unique_owner_for_site_matching(
        &self,
        callsite: CallsiteKey,
        accept: impl Fn(&CallResultFact, &r2ssa::ValueOwner) -> bool,
    ) -> Result<Option<&r2ssa::ValueOwner>, ()> {
        let mut selected = None;
        for result in self.results_for_site(callsite) {
            let Some(owner) = result.owner.as_ref().filter(|owner| accept(result, owner)) else {
                continue;
            };
            if selected.is_some_and(|existing| existing != owner) {
                return Err(());
            }
            selected = Some(owner);
        }
        Ok(selected)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionCallRenderFacts {
    pub by_callsite: BTreeMap<CallsiteKey, CallsiteRenderFact>,
}

impl FunctionCallRenderFacts {
    pub fn is_empty(&self) -> bool {
        self.by_callsite.is_empty()
    }

    pub fn fact_for_site(&self, callsite: CallsiteKey) -> Option<&CallsiteRenderFact> {
        self.by_callsite.get(&callsite)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallsiteRenderFact {
    pub callsite: CallsiteKey,
    pub target: Option<r2ssa::ValueId>,
    pub disposition: CallsiteRenderDisposition,
    pub proof_values: Vec<r2ssa::ValueId>,
    pub residual_reason: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CallsiteRenderDisposition {
    SideEffectStatement,
    AssignedResult,
    NestedExpression,
    /// A value-returning callee returns directly to this function's caller.
    TerminalReturn,
    /// A void callee returns directly to this function's caller.
    TerminalVoidReturn,
    Suppressed,
    Residualized,
}

impl CallsiteRenderDisposition {
    pub const fn is_terminal_return(self) -> bool {
        matches!(self, Self::TerminalReturn | Self::TerminalVoidReturn)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionControlFacts {
    pub branch_predicates: BTreeMap<u64, BranchPredicateFact>,
    pub block_assumptions: BTreeMap<u64, Vec<ControlBlockAssumptionFact>>,
    pub loops: BTreeMap<r2ssa::LoopId, LoopStructureFact>,
    pub switches: BTreeMap<u64, SwitchSelectorFact>,
    pub control_domains: r2ssa::ControlDomainFacts,
}

impl FunctionControlFacts {
    pub fn is_empty(&self) -> bool {
        self.branch_predicates.is_empty()
            && self.block_assumptions.is_empty()
            && self.loops.is_empty()
            && self.switches.is_empty()
            && self.control_domains.by_block.is_empty()
    }

    pub fn branch_for_block(&self, block_addr: u64) -> Option<&BranchPredicateFact> {
        self.branch_predicates.get(&block_addr)
    }

    pub fn switch_for_block(&self, block_addr: u64) -> Option<&SwitchSelectorFact> {
        self.switches.get(&block_addr)
    }

    pub fn control_domain_for_block(&self, block_addr: u64) -> Option<&r2ssa::ControlDomain> {
        self.control_domains.for_block(block_addr)
    }

    pub fn loops_for_header(&self, header: u64) -> impl Iterator<Item = &LoopStructureFact> + '_ {
        self.loops
            .values()
            .filter(move |fact| fact.header == header)
    }

    pub fn assumptions_for_block(
        &self,
        block_addr: u64,
    ) -> impl Iterator<Item = &ControlBlockAssumptionFact> {
        self.block_assumptions
            .get(&block_addr)
            .into_iter()
            .flatten()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionRenderFacts {
    /// Canonical certified expression graph keyed by stable semantic identity.
    pub certified_exprs: BTreeMap<r2ssa::SemanticId, CertifiedExpr>,
    /// Canonical certified addressable entities keyed by stable semantic identity.
    pub certified_entities: BTreeMap<r2ssa::SemanticId, CertifiedEntity>,
    /// Canonical certified observable-effect graph keyed by stable semantic identity.
    pub certified_effects: BTreeMap<r2ssa::SemanticId, CertifiedEffect>,
    /// Stable return-effect identity for each canonical SSA op site.
    pub return_effects_by_op: BTreeMap<OpSiteKey, r2ssa::SemanticId>,
    /// Stable memory-effect identities for each canonical SSA op site.
    pub memory_effects_by_op: BTreeMap<MemoryOpSiteKey, Vec<r2ssa::SemanticId>>,
    /// Value annotations that supplement, rather than duplicate, certified expressions.
    pub string_literals_by_value: BTreeMap<r2ssa::ValueId, StringLiteralRenderFact>,
    /// Type-owner render projections tied back to canonical memory-effect identities.
    pub member_accesses_by_op: BTreeMap<MemoryOpSiteKey, Vec<MemberAccessRenderFact>>,
    pub array_accesses_by_op: BTreeMap<MemoryOpSiteKey, Vec<ArrayAccessRenderFact>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSlotOwnerRenderAuthorization {
    pub object: r2ssa::ObjectId,
    pub offset: i64,
    pub name: String,
}

impl FunctionRenderFacts {
    /// Project one prepared SSA artifact into the canonical render contract.
    ///
    /// This is the only owner for translating prepared certificates into
    /// certified expressions, entities, effects, and op-site indexes.
    fn from_prepared(prepared: &r2ssa::SsaArtifact) -> Self {
        prepared_render_facts(prepared)
    }

    pub fn is_empty(&self) -> bool {
        self.certified_exprs.is_empty()
            && self.certified_entities.is_empty()
            && self.certified_effects.is_empty()
            && self.return_effects_by_op.is_empty()
            && self.memory_effects_by_op.is_empty()
            && self.string_literals_by_value.is_empty()
            && self.member_accesses_by_op.is_empty()
            && self.array_accesses_by_op.is_empty()
    }

    pub fn expression_for_value(&self, value: r2ssa::ValueId) -> Option<&ExpressionRenderFact> {
        self.certified_exprs
            .get(&r2ssa::SemanticId::expression(value))
            .map(|cert| &cert.fact)
    }

    pub fn certified_expr_for_value(&self, value: r2ssa::ValueId) -> Option<&CertifiedExpr> {
        self.certified_exprs
            .get(&r2ssa::SemanticId::expression(value))
    }

    pub fn guarded_phi_for_value(&self, value: r2ssa::ValueId) -> Option<&GuardedPhiRenderFact> {
        self.certified_expr_for_value(value)?.guarded_phi.as_ref()
    }

    pub fn certified_effect(&self, id: r2ssa::SemanticId) -> Option<&CertifiedEffect> {
        self.certified_effects.get(&id)
    }

    pub fn parameter_values(&self, slot: usize) -> impl Iterator<Item = r2ssa::ValueId> + '_ {
        let entity =
            r2ssa::SemanticId::parameter(slot).and_then(|id| self.certified_entities.get(&id));
        entity
            .into_iter()
            .flat_map(|entity| match entity {
                CertifiedEntity::Parameter { entry_values, .. } => Some(entry_values),
                CertifiedEntity::StackSlot { .. } | CertifiedEntity::LoopCarrier { .. } => None,
            })
            .flatten()
            .copied()
    }

    pub fn has_certified_parameter(&self, slot: usize) -> bool {
        let Some(id) = r2ssa::SemanticId::parameter(slot) else {
            return false;
        };
        matches!(
            self.certified_entities.get(&id),
            Some(CertifiedEntity::Parameter {
                slot: entity_slot,
                ..
            }) if usize::try_from(*entity_slot).ok() == Some(slot)
        )
    }

    /// Resolve a value carrying a direct parameter binding to one ABI slot.
    ///
    /// This deliberately does not walk expression inputs: an expression that
    /// depends on one parameter is not necessarily identical to that parameter.
    pub fn exact_parameter_slot_for_value(&self, value: r2ssa::ValueId) -> Option<usize> {
        let expr = self.certified_expr_for_value(value)?;
        let mut slots = expr.bindings.iter().filter_map(|binding| {
            let r2ssa::SemanticId::Parameter(slot) = binding else {
                return None;
            };
            match self.certified_entities.get(binding) {
                Some(CertifiedEntity::Parameter {
                    slot: entity_slot, ..
                }) if entity_slot == slot => usize::try_from(*slot).ok(),
                _ => None,
            }
        });
        let slot = slots.next()?;
        slots.next().is_none().then_some(slot)
    }

    /// Resolve an expression to one unambiguous ABI parameter dependency.
    ///
    /// The walk follows only the certified expression graph and its stable
    /// `SemanticId::Parameter` bindings. Rendered names and register spellings
    /// are deliberately excluded.
    pub fn unique_parameter_dependency_slot_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<usize> {
        let mut pending = vec![r2ssa::SemanticId::expression(value)];
        let mut visited = BTreeSet::new();
        let mut slots = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            let Some(expr) = self.certified_exprs.get(&id) else {
                continue;
            };
            for binding in &expr.bindings {
                if let r2ssa::SemanticId::Parameter(slot) = binding {
                    slots.insert(usize::try_from(*slot).ok()?);
                }
            }
            pending.extend(expr.inputs.iter().copied());
        }
        let slot = slots.pop_first()?;
        slots.is_empty().then_some(slot)
    }

    pub fn return_effect_id_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
    ) -> Option<r2ssa::SemanticId> {
        self.return_effects_by_op
            .get(&(block_addr, op_index))
            .copied()
    }

    pub fn memory_effect_id_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        space: r2il::SpaceId,
        address: r2ssa::ValueId,
        value: Option<r2ssa::ValueId>,
    ) -> Option<r2ssa::SemanticId> {
        let mut matching = self
            .memory_effects_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .filter_map(|id| match self.certified_effects.get(id) {
                Some(CertifiedEffect::Memory { fact, .. })
                    if fact.space == space && fact.address == address && fact.value == value =>
                {
                    Some(*id)
                }
                _ => None,
            });
        let first = matching.next()?;
        matching.next().is_none().then_some(first)
    }

    pub fn expression_is_renderable(&self, value: r2ssa::ValueId) -> bool {
        self.expression_for_value(value)
            .is_some_and(|fact| fact.renderable)
    }

    pub fn string_literal_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&StringLiteralRenderFact> {
        self.string_literals_by_value.get(&value)
    }

    pub fn memory_access_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        space: r2il::SpaceId,
    ) -> Option<&MemoryAccessRenderFact> {
        let mut matching = self
            .memory_effects_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .filter_map(|id| {
                self.certified_effects
                    .get(id)
                    .and_then(CertifiedEffect::memory_fact)
            })
            .filter(|fact| fact.space == space && fact.width > 0);
        let first = matching.next()?;
        matching.next().is_none().then_some(first)
    }

    pub fn memory_access(
        &self,
        access: r2ssa::StructuredAccessId,
    ) -> Option<&MemoryAccessRenderFact> {
        self.certified_effects
            .get(&r2ssa::SemanticId::memory_access(access))
            .and_then(CertifiedEffect::memory_fact)
    }

    pub fn memory_accesses(&self) -> impl Iterator<Item = &MemoryAccessRenderFact> {
        self.certified_effects
            .values()
            .filter_map(CertifiedEffect::memory_fact)
    }

    pub fn member_access(
        &self,
        access: r2ssa::StructuredAccessId,
    ) -> Option<&MemberAccessRenderFact> {
        let memory = self.memory_access(access)?;
        let facts = self.member_accesses_by_op.get(&(
            memory.block_addr,
            memory.op_index,
            memory.is_write,
        ))?;
        let mut matching = facts.iter().filter(|fact| {
            fact.access == memory.access
                && fact.object == memory.object
                && fact.access_width == memory.width
        });
        let first = matching.next()?;
        matching.next().is_none().then_some(first)
    }

    pub fn memory_value_type(&self, access: r2ssa::StructuredAccessId) -> Option<&CTypeLike> {
        self.member_access(access)?.field_type.as_ref()
    }

    pub fn return_effects(&self) -> impl Iterator<Item = &ReturnValueRenderFact> {
        self.certified_effects
            .values()
            .filter_map(CertifiedEffect::return_fact)
    }

    pub fn stack_slot(
        &self,
        object: r2ssa::ObjectId,
    ) -> Option<(r2ssa::StackAddressBase, i64, Option<u32>)> {
        match self
            .certified_entities
            .get(&r2ssa::SemanticId::stack_slot(object))?
        {
            CertifiedEntity::StackSlot {
                base, offset, size, ..
            } => Some((*base, *offset, *size)),
            CertifiedEntity::Parameter { .. } | CertifiedEntity::LoopCarrier { .. } => None,
        }
    }

    pub fn stack_slot_offset(&self, object: r2ssa::ObjectId) -> Option<i64> {
        self.stack_slot(object).map(|(_, offset, _)| offset)
    }

    pub fn stack_slots(
        &self,
    ) -> impl Iterator<Item = (r2ssa::ObjectId, r2ssa::StackAddressBase, i64, Option<u32>)> + '_
    {
        self.certified_entities
            .values()
            .filter_map(|entity| match entity {
                CertifiedEntity::StackSlot {
                    object,
                    base,
                    offset,
                    size,
                    ..
                } => Some((*object, *base, *offset, *size)),
                CertifiedEntity::Parameter { .. } | CertifiedEntity::LoopCarrier { .. } => None,
            })
    }

    pub fn loop_carrier_for_value(&self, value: r2ssa::ValueId) -> Option<&CertifiedEntity> {
        let expr = self.certified_expr_for_value(value)?;
        let mut carriers = expr.bindings.iter().filter_map(|binding| {
            let r2ssa::SemanticId::LoopCarrier(_) = binding else {
                return None;
            };
            match self.certified_entities.get(binding) {
                Some(entity @ CertifiedEntity::LoopCarrier { members, .. })
                    if members
                        .binary_search_by_key(&value, |member| member.value)
                        .is_ok() =>
                {
                    Some(entity)
                }
                _ => None,
            }
        });
        let carrier = carriers.next()?;
        carriers.next().is_none().then_some(carrier)
    }

    pub fn loop_carrier_update_for_value_at_latch(
        &self,
        value: r2ssa::ValueId,
        latch: u64,
    ) -> Option<&CertifiedEntity> {
        let expr = self.certified_expr_for_value(value)?;
        let mut carriers = expr.bindings.iter().filter_map(|binding| {
            let r2ssa::SemanticId::LoopCarrier(_) = binding else {
                return None;
            };
            match self.certified_entities.get(binding) {
                Some(entity @ CertifiedEntity::LoopCarrier { updates, .. })
                    if updates.iter().any(|update| {
                        update.predecessor == latch
                            && (update.value == value || update.identity_values.contains(&value))
                    }) =>
                {
                    Some(entity)
                }
                _ => None,
            }
        });
        let carrier = carriers.next()?;
        carriers.next().is_none().then_some(carrier)
    }

    pub fn loop_carrier_update_for_value(&self, value: r2ssa::ValueId) -> Option<&CertifiedEntity> {
        let expr = self.certified_expr_for_value(value)?;
        let mut carriers = expr.bindings.iter().filter_map(|binding| {
            let r2ssa::SemanticId::LoopCarrier(_) = binding else {
                return None;
            };
            match self.certified_entities.get(binding) {
                Some(entity @ CertifiedEntity::LoopCarrier { updates, .. })
                    if updates.iter().any(|update| {
                        update.value == value || update.identity_values.contains(&value)
                    }) =>
                {
                    Some(entity)
                }
                _ => None,
            }
        });
        let carrier = carriers.next()?;
        carriers.next().is_none().then_some(carrier)
    }

    pub fn loop_carriers(&self) -> impl Iterator<Item = &CertifiedEntity> {
        self.certified_entities
            .values()
            .filter(|entity| matches!(entity, CertifiedEntity::LoopCarrier { .. }))
    }

    pub fn return_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
    ) -> Option<&ReturnValueRenderFact> {
        self.return_effect_id_for_op(block_addr, op_index)
            .and_then(|id| self.certified_effects.get(&id))
            .and_then(CertifiedEffect::return_fact)
    }

    pub fn member_access_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        field_name: &str,
        field_offset: u64,
        access_width: Option<u32>,
    ) -> Option<&MemberAccessRenderFact> {
        self.member_accesses_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .find(|fact| {
                let Some(memory) = self.memory_access(fact.access) else {
                    return false;
                };
                memory.block_addr == block_addr
                    && memory.op_index == op_index
                    && memory.is_write == is_write
                    && memory.object == fact.object
                    && memory.width == fact.access_width
                    && fact.field_offset == field_offset
                    && fact.field_name.eq_ignore_ascii_case(field_name)
                    && access_width.is_none_or(|width| fact.access_width == width)
            })
    }

    pub fn member_access_for_op_any_direction(
        &self,
        block_addr: u64,
        op_index: usize,
        field_name: &str,
        field_offset: u64,
        access_width: Option<u32>,
    ) -> Option<&MemberAccessRenderFact> {
        self.member_access_for_op(
            block_addr,
            op_index,
            false,
            field_name,
            field_offset,
            access_width,
        )
        .or_else(|| {
            self.member_access_for_op(
                block_addr,
                op_index,
                true,
                field_name,
                field_offset,
                access_width,
            )
        })
    }

    pub fn array_access_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        field_offset: u64,
        element_stride: u64,
        access_width: Option<u32>,
    ) -> Option<&ArrayAccessRenderFact> {
        self.array_accesses_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .find(|fact| {
                let Some(memory) = self.memory_access(fact.access) else {
                    return false;
                };
                memory.block_addr == block_addr
                    && memory.op_index == op_index
                    && memory.is_write == is_write
                    && memory.object == fact.object
                    && memory.width == fact.access_width
                    && fact.field_offset == field_offset
                    && fact.element_stride == element_stride
                    && access_width.is_none_or(|width| fact.access_width == width)
            })
    }

    pub fn array_access_for_op_any_direction(
        &self,
        block_addr: u64,
        op_index: usize,
        field_offset: u64,
        element_stride: u64,
        access_width: Option<u32>,
    ) -> Option<&ArrayAccessRenderFact> {
        self.array_access_for_op(
            block_addr,
            op_index,
            false,
            field_offset,
            element_stride,
            access_width,
        )
        .or_else(|| {
            self.array_access_for_op(
                block_addr,
                op_index,
                true,
                field_offset,
                element_stride,
                access_width,
            )
        })
    }

    pub fn has_stack_slot_offset(&self, offset: i64) -> bool {
        self.stack_slots()
            .any(|(_, _, slot_offset, _)| slot_offset == offset)
    }
}

fn stack_slot_offset(slot: &StackSlotKey) -> i64 {
    slot.offset
}

fn stack_slot_matches_offset(slot: &StackSlotKey, offset: i64) -> bool {
    stack_slot_offset(slot) == offset
}

fn visible_stack_binding_kind_is_renderable(kind: &VisibleBindingKind) -> bool {
    matches!(
        kind,
        VisibleBindingKind::Param | VisibleBindingKind::Local | VisibleBindingKind::StackObject
    )
}

fn external_stack_slot_role_is_renderable(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::Local | ExternalStackSlotRole::StackArg
    )
}

fn recovered_stack_owner_name_is_renderable(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    !lower.is_empty()
        && lower != "stack"
        && lower != "slot"
        && lower != "saved_fp"
        && lower != "fake_stack_slot"
        && !lower.starts_with("stack_")
        && !lower.starts_with("slot_")
        && !lower.starts_with("local_")
        && !lower.starts_with("arg_")
        && !lower.starts_with("var_")
}

fn remember_stack_param_owner_name(candidate: &mut Option<String>, name: &str) -> Option<()> {
    let name = name.trim();
    if name.is_empty() {
        return Some(());
    }
    if let Some(existing) = candidate.as_ref() {
        return existing.eq_ignore_ascii_case(name).then_some(());
    }
    *candidate = Some(name.to_string());
    Some(())
}

fn stack_owner_type_is_renderable(ty: &CTypeLike) -> bool {
    !matches!(ty, CTypeLike::Unknown | CTypeLike::Void)
}

fn signature_param_name_type_is_renderable(
    signature: Option<&FunctionSignatureSpec>,
    name: &str,
) -> bool {
    signature
        .into_iter()
        .flat_map(|signature| signature.params.iter())
        .any(|param| {
            param.name.eq_ignore_ascii_case(name)
                && param
                    .ty
                    .as_ref()
                    .is_some_and(stack_owner_type_is_renderable)
        })
}

fn indexed_param_home_name<'a>(
    signature: Option<&'a FunctionSignatureSpec>,
    slot: &ExternalStackSlotSpec,
) -> Option<&'a str> {
    if !matches!(slot.role, ExternalStackSlotRole::ParamHome) {
        return None;
    }
    let param = signature?.params.get(slot.param_index?)?;
    let name = param.name.trim();
    (!name.is_empty()
        && param
            .ty
            .as_ref()
            .is_some_and(stack_owner_type_is_renderable))
    .then_some(name)
}

pub(crate) fn type_like_size_bytes(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Void
        | CTypeLike::Unknown
        | CTypeLike::BitVector(_)
        | CTypeLike::Function { .. } => None,
        CTypeLike::Bool => Some(1),
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        CTypeLike::Pointer(_) => Some((ptr_bits / 8).max(1) as u64),
        CTypeLike::Array(inner, Some(count)) => {
            type_like_size_bytes(inner, ptr_bits).map(|size| size.saturating_mul(*count as u64))
        }
        CTypeLike::Array(inner, None) => type_like_size_bytes(inner, ptr_bits),
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) | CTypeLike::Typedef(_) => {
            None
        }
    }
}

/// The exact storage width a C declaration type describes.
pub fn declaration_type_width_bits(ty: &CTypeLike, ptr_bits: u32) -> Option<u32> {
    match ty {
        CTypeLike::Int {
            bits,
            signedness: crate::Signedness::Signed | crate::Signedness::Unsigned,
        }
        | CTypeLike::Float(bits)
            if *bits <= 128 =>
        {
            Some(*bits)
        }
        CTypeLike::Pointer(_) => Some(ptr_bits),
        CTypeLike::Array(element, Some(count)) => {
            declaration_type_width_bits(element, ptr_bits)?.checked_mul(u32::try_from(*count).ok()?)
        }
        CTypeLike::BitVector(bits) if *bits > 128 => Some(*bits),
        CTypeLike::Typedef(name) => crate::parse_external_type_like_spec(name, ptr_bits)
            .and_then(|parsed| parsed.bits(ptr_bits)),
        _ => None,
    }
}

/// Admit a logical type only where it describes this exact storage width.
pub fn admit_declaration_type(ty: CTypeLike, width_bits: u32, ptr_bits: u32) -> CTypeLike {
    let admissible = match &ty {
        CTypeLike::Pointer(_) => width_bits == ptr_bits,
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => *bits == width_bits,
        CTypeLike::Typedef(name) => {
            crate::parse_external_type_like_spec(name, ptr_bits)
                .and_then(|parsed| parsed.bits(ptr_bits))
                == Some(width_bits)
        }
        _ => false,
    };
    if admissible {
        ty
    } else {
        CTypeLike::machine_bits(width_bits)
    }
}

fn function_type_matches_source_interface(
    signature: &crate::FunctionType,
    interface: &r2ssa::SourceFunctionInterface,
    ptr_bits: u32,
) -> bool {
    if ptr_bits == 0 || signature.params.len() != interface.parameters().len() {
        return false;
    }
    let parameter_widths_match = signature.params.iter().enumerate().all(|(index, ty)| {
        let Some(actual_bits) = declaration_type_width_bits(ty, ptr_bits).map(u64::from) else {
            return false;
        };
        let expected_bits = interface
            .parameter_logical_values()
            .get(index)
            .map(|logical| logical.carrier().size_bits())
            .or_else(|| {
                interface
                    .parameters()
                    .get(index)
                    .map(|parameter| u64::from(parameter.storage().size) * 8)
            });
        expected_bits == Some(actual_bits)
    });
    if !parameter_widths_match {
        return false;
    }
    match (interface.return_kind(), &signature.return_type) {
        (r2ssa::SourceFunctionReturn::Void, CTypeLike::Void) => true,
        (r2ssa::SourceFunctionReturn::Register { storage }, ty) => {
            let actual_bits = declaration_type_width_bits(ty, ptr_bits).map(u64::from);
            let expected_bits = interface
                .return_logical_value()
                .map(|logical| logical.carrier().size_bits())
                .or_else(|| Some(u64::from(storage.size) * 8));
            actual_bits == expected_bits
        }
        _ => false,
    }
}

fn field_certificate_width_matches(
    cert: &crate::facts::FieldAccessCertificate,
    access_width: u32,
    ptr_bits: u32,
) -> bool {
    cert.field_type
        .as_deref()
        .and_then(|field_type| parse_c_type_like(field_type, ptr_bits))
        .and_then(|ty| type_like_size_bytes(&ty, ptr_bits))
        .is_none_or(|width| width == u64::from(access_width))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionRenderFact {
    pub value: r2ssa::ValueId,
    pub defining_inst: Option<r2ssa::InstId>,
    pub width: u32,
    pub renderable: bool,
}

/// A renderable expression tied to canonical SSA identity and dependencies.
///
/// `bindings` records semantic roles such as ABI parameters without replacing
/// the expression's stable value identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedExpr {
    pub id: r2ssa::SemanticId,
    pub fact: ExpressionRenderFact,
    pub inputs: Vec<r2ssa::SemanticId>,
    pub bindings: BTreeSet<r2ssa::SemanticId>,
    pub guarded_phi: Option<GuardedPhiRenderFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardedPhiRenderFact {
    pub predicate: r2ssa::SemanticId,
    pub when_true: GuardedPhiArmRenderFact,
    pub when_false: GuardedPhiArmRenderFact,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardedPhiArmRenderFact {
    pub sources: Vec<r2ssa::SemanticId>,
    pub rendered: r2ssa::SemanticId,
}

/// A certified addressable resource. Resources have identity and layout but do
/// not execute, so they must never be counted as observable effects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertifiedEntity {
    Parameter {
        id: r2ssa::SemanticId,
        slot: u32,
        entry_values: BTreeSet<r2ssa::ValueId>,
        carrier_width: u32,
        /// Exact logical type from the immutable source interface. Absence is
        /// unknown and must not be repaired from a merged renderer signature.
        ty: Option<CTypeLike>,
    },
    StackSlot {
        id: r2ssa::SemanticId,
        object: r2ssa::ObjectId,
        base: r2ssa::StackAddressBase,
        offset: i64,
        size: Option<u32>,
        array_layout: r2ssa::StackArrayLayoutDisposition,
        /// Full source slot identity, including its local/parameter-home role.
        /// Absence grants no source-variable identity; a separate upstream
        /// callee-allocation proof is required for an anonymous C object.
        source_slot: Option<r2ssa::SourceStackSlotSpec>,
        /// Upstream proof for a compiler-created, source-less callee-owned
        /// stack object. Consumers may use it but must not reconstruct it.
        callee_allocation: Option<r2ssa::CalleeStackAllocationCertificate>,
    },
    LoopCarrier {
        id: r2ssa::SemanticId,
        loop_id: r2ssa::LoopId,
        header: u64,
        phi: r2ssa::ValueId,
        width: u32,
        identity_values: BTreeSet<r2ssa::ValueId>,
        entries: Vec<r2ssa::LoopCarrierEdgeValue>,
        updates: Vec<r2ssa::LoopCarrierUpdateFact>,
        dominating_initializers: Vec<r2ssa::LoopCarrierEdgeValue>,
        members: Vec<r2ssa::LoopCarrierMemberFact>,
        ty: Option<CTypeLike>,
    },
}

impl CertifiedEntity {
    pub const fn id(&self) -> r2ssa::SemanticId {
        match self {
            Self::Parameter { id, .. }
            | Self::StackSlot { id, .. }
            | Self::LoopCarrier { id, .. } => *id,
        }
    }

    /// Canonical SSA values that may name one mutable renderer binding.
    ///
    /// Membership is program-point sensitive: entry values, loop updates, and
    /// dominating initializers may participate only when lowering preserves the
    /// assignments at their original definition sites. This certificate does
    /// not authorize globally substituting any member's expression with the
    /// binding. Stack-slot entities return `None` because object identity alone
    /// is not a certificate of `ValueId` membership.
    pub fn coalescing_values(&self) -> Option<BTreeSet<r2ssa::ValueId>> {
        match self {
            Self::Parameter { entry_values, .. } => Some(entry_values.clone()),
            Self::LoopCarrier { members, .. } => {
                Some(members.iter().map(|member| member.value).collect())
            }
            Self::StackSlot { .. } => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CertifiedEffectKind {
    MemoryRead,
    MemoryWrite,
    Return,
}

/// A certified observable effect or addressable resource.
///
/// Variants retain the typed canonical payload, so consumers never need to
/// recover semantic identity from rendered text or tuple-shaped sidecars.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertifiedEffect {
    Memory {
        id: r2ssa::SemanticId,
        fact: MemoryAccessRenderFact,
    },
    Return {
        id: r2ssa::SemanticId,
        at: r2ssa::InstId,
        fact: ReturnValueRenderFact,
    },
}

impl CertifiedEffect {
    pub const fn id(&self) -> r2ssa::SemanticId {
        match self {
            Self::Memory { id, .. } | Self::Return { id, .. } => *id,
        }
    }

    pub const fn kind(&self) -> CertifiedEffectKind {
        match self {
            Self::Memory { fact, .. } if fact.is_write => CertifiedEffectKind::MemoryWrite,
            Self::Memory { .. } => CertifiedEffectKind::MemoryRead,
            Self::Return { .. } => CertifiedEffectKind::Return,
        }
    }

    pub const fn control_domain(&self) -> &r2ssa::ControlDomain {
        match self {
            Self::Memory { fact, .. } => &fact.control_domain,
            Self::Return { fact, .. } => &fact.control_domain,
        }
    }

    pub const fn memory_fact(&self) -> Option<&MemoryAccessRenderFact> {
        match self {
            Self::Memory { fact, .. } => Some(fact),
            _ => None,
        }
    }

    pub const fn return_fact(&self) -> Option<&ReturnValueRenderFact> {
        match self {
            Self::Return { fact, .. } => Some(fact),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryAccessRenderFact {
    pub access: r2ssa::StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub space: r2il::SpaceId,
    pub object: r2ssa::ObjectId,
    pub address: r2ssa::ValueId,
    pub value: Option<r2ssa::ValueId>,
    pub is_write: bool,
    pub width: u32,
    /// True when one certified expression root contains multiple paths to this
    /// read and would duplicate the effect if rendered inline.
    pub materialize_result: bool,
    pub control_domain: r2ssa::ControlDomain,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteralRenderFact {
    pub value: r2ssa::ValueId,
    pub address: u64,
    pub text: String,
    pub source: StringLiteralRenderSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringLiteralRenderSource {
    TypedFunctionFacts,
    Radare2TypedCollector,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemberAccessRenderFact {
    pub access: r2ssa::StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: r2ssa::ObjectId,
    pub is_write: bool,
    pub field_offset: u64,
    pub field_name: String,
    pub field_type: Option<CTypeLike>,
    pub access_width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayAccessRenderFact {
    pub access: r2ssa::StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: r2ssa::ObjectId,
    pub is_write: bool,
    pub field_offset: u64,
    pub element_stride: u64,
    pub access_width: u32,
    pub base: Option<r2ssa::SemanticId>,
    pub index: Option<r2ssa::SemanticId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnValueRenderFact {
    pub block_addr: u64,
    pub op_index: usize,
    pub value: r2ssa::ValueId,
    pub width: u32,
    /// Ordered contained-slice writes over `value`, empty for an ordinary
    /// return. See `r2ssa::ReturnValueCertificate::overlays`: when this is not
    /// empty `value` is the base rather than the whole returned value.
    pub overlays: Vec<r2ssa::ReturnValueOverlay>,
    pub control_domain: r2ssa::ControlDomain,
}

impl ReturnValueRenderFact {
    /// Every value this return carries, base first and overlays in order.
    pub fn values(&self) -> impl Iterator<Item = r2ssa::ValueId> + '_ {
        std::iter::once(self.value).chain(self.overlays.iter().map(|overlay| overlay.value))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchPredicateFact {
    pub id: r2ssa::PredicateId,
    pub block_addr: u64,
    pub condition: r2ssa::ValueId,
    pub comparison: Option<PredicateComparisonFact>,
    pub evaluated_comparison: Option<PredicateComparisonFact>,
    /// Comparison selected by prepared semantics for rendering at the source
    /// branch program point.
    pub render_comparison: Option<PredicateComparisonFact>,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PredicateComparisonFact {
    pub kind: r2ssa::CompareKind,
    pub lhs: r2ssa::ValueId,
    pub rhs: r2ssa::ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ControlBlockAssumptionFact {
    pub predecessor: u64,
    pub predicate: r2ssa::PredicateId,
    pub truth: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopStructureFact {
    pub loop_id: r2ssa::LoopId,
    pub proof_node: String,
    pub header: u64,
    pub condition: Option<r2ssa::PredicateId>,
    pub condition_value: Option<r2ssa::ValueId>,
    pub body: Vec<u64>,
    pub latches: Vec<u64>,
    pub exits: Vec<u64>,
    pub for_loop: Option<r2ssa::ForLoopCertificate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchSelectorFact {
    pub proof_node: String,
    pub block_addr: u64,
    pub selector: Option<r2ssa::ValueId>,
    pub cases: Vec<(u64, u64)>,
    pub default: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallResultFact {
    pub callsite: CallsiteKey,
    pub call_site_id: r2ssa::CallSiteId,
    pub at: r2ssa::InstId,
    pub value: r2ssa::ValueId,
    pub width: u32,
    pub relation: r2ssa::CallResultValueRelation,
    pub carrier: r2ssa::ReturnCarrier,
    pub owner: Option<r2ssa::ValueOwner>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallsiteArgumentFacts {
    pub callsite: CallsiteKey,
    pub call_site_id: r2ssa::CallSiteId,
    pub at: r2ssa::InstId,
    pub target: r2ssa::ValueId,
    pub direct_target: Option<u64>,
    pub argument_values: Vec<CallArgumentValueFact>,
    /// Whether the callee takes a variadic tail, as the source's prototype for
    /// it says. Two call sites of one variadic callee legitimately pass
    /// different numbers of arguments, and the declaration a rendering owes
    /// the callee has to say so or it cannot describe both.
    pub variadic: bool,
    /// How many leading `argument_values` the callee's prototype names, where
    /// a prototype described the call. The rest are the variadic tail.
    pub fixed_argument_count: Option<usize>,
    /// Exact logical signature projected from a callee body in the same
    /// source-owned capture. Its carrier contract has already been checked
    /// against this call site by `r2ssa`.
    pub callee_signature: Option<crate::FunctionType>,
    /// Per-callsite argument-count proof for a variadic call. This is absent
    /// for fixed calls and never inferred from live argument registers.
    pub variadic_argument_count_evidence: Option<r2ssa::VariadicCallsiteArgumentCountEvidence>,
    pub variadic_argument_count_refusal: Option<r2ssa::VariadicCallsiteArgumentCountRefusal>,
    pub register_argument_locations: Vec<RegisterCallArgumentLocationFact>,
    pub stack_argument_locations: Vec<StackCallArgumentLocationFact>,
}

impl CallsiteArgumentFacts {
    pub fn argument_value(&self, index: usize) -> Option<r2ssa::ValueId> {
        self.argument_values
            .iter()
            .find(|argument| argument.index == index)
            .map(|argument| argument.value)
    }

    pub fn canonical_argument_values(&self) -> Vec<r2ssa::ValueId> {
        let mut by_index = BTreeMap::new();
        for argument in &self.argument_values {
            by_index.insert(argument.index, argument.value);
        }
        for argument in &self.stack_argument_locations {
            by_index.entry(argument.index).or_insert(argument.value);
        }
        by_index.into_values().collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallArgumentValueFact {
    pub index: usize,
    pub value: r2ssa::ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegisterCallArgumentLocationFact {
    pub index: usize,
    pub value: r2ssa::ValueId,
    pub storage: r2ssa::CanonicalStorageId,
    pub source_inst: Option<r2ssa::InstId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StackCallArgumentLocationFact {
    pub index: usize,
    pub value: r2ssa::ValueId,
    pub object: r2ssa::ObjectId,
    pub offset: i64,
    pub memory_access: r2ssa::StructuredAccessId,
    pub source_inst: Option<r2ssa::InstId>,
}

impl AnalysisPlans {
    pub fn from_semantics(semantics: Option<&r2sym::SemanticArtifactReport>) -> Self {
        let Some(semantics) = semantics else {
            return Self::default();
        };
        Self {
            artifact_build: Some(semantics.build_plan()),
            query: Some(semantics.query_plan()),
            type_plan: Some(semantics.type_plan()),
            decompile: Some(semantics.decompile_plan()),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct InterprocSummaryView {
    #[serde(skip_serializing_if = "Option::is_none")]
    set: Option<r2ssa::InterprocSummarySet>,
    #[serde(skip_serializing_if = "Option::is_none")]
    rollup: Option<SummaryEffectRollup>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    helpers: Vec<SummaryHelperView>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryEffectRollup {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_return_relation: Option<r2ssa::SummaryReturnRelation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub out_param_facts: Vec<SummaryOutParamFact>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    #[serde(default)]
    pub transfer_count: usize,
    #[serde(default)]
    pub allocation_count: usize,
    #[serde(default)]
    pub lifetime_count: usize,
    #[serde(default)]
    pub sync_count: usize,
    #[serde(default)]
    pub atomic_count: usize,
    pub helper_summary_count: usize,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryHelperView {
    pub function_id: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arg_count_hint: Option<usize>,
    pub return_relation: r2ssa::SummaryReturnRelation,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub out_param_facts: Vec<SummaryOutParamFact>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub transfer_effects: Vec<r2ssa::SummaryTransferEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allocation_effects: Vec<r2ssa::SummaryAllocationEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lifetime_effects: Vec<r2ssa::SummaryLifetimeEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sync_effects: Vec<r2ssa::SummarySyncEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub atomic_effects: Vec<r2ssa::SummaryAtomicEffect>,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryOutParamFact {
    pub param_index: usize,
    pub evidence: OutParamCertificateEvidence,
    pub source: OutParamCertificateSource,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileCapabilityView {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub plan: Option<r2sym::DecompilePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slice_class: Option<r2sym::SliceClass>,
    pub skipped_large_cfg: bool,
    pub has_native_regions: bool,
    pub has_summary_islands: bool,
    pub has_primary_summary_islands: bool,
    pub summary_island_count: usize,
    pub primary_summary_island_count: usize,
    pub generic_memory_summary_count: usize,
    pub has_memory_read_write_summary_pair: bool,
    pub actionable_region_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ambiguous_targets: Vec<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<r2sym::ResidualReason>,
    pub assumption_conflicted: bool,
    pub summary_conflicted: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DecompileRouteKind {
    Standard,
    StructuredWorker,
    SummaryIslands,
    LinearWorker,
    VmSummary,
    FallbackComment,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileRouteFacts {
    pub kind: DecompileRouteKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fallback_comment: Option<String>,
    pub use_prepared_semantic_view: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionInputQualityFacts {
    pub expected_blocks: usize,
    pub lifted_blocks: usize,
    pub actual_lifted_blocks: usize,
    pub read_failures: usize,
    pub invalid_blocks: usize,
    pub null_lift_failures: usize,
    pub truncated_blocks: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refusal_reason: Option<String>,
}

impl FunctionInputQualityFacts {
    pub fn is_complete(&self) -> bool {
        self.refusal_reason.is_none()
            && self.expected_blocks > 0
            && self.lifted_blocks > 0
            && self.expected_blocks == self.lifted_blocks
            && self.lifted_blocks == self.actual_lifted_blocks
            && self.read_failures == 0
            && self.invalid_blocks == 0
            && self.null_lift_failures == 0
            && self.truncated_blocks == 0
    }
}

impl InterprocSummaryView {
    pub fn new(
        set: Option<r2ssa::InterprocSummarySet>,
    ) -> Result<Self, r2ssa::interproc::InterprocSummarySchemaError> {
        if let Some(set) = set.as_ref() {
            set.validate_current_schema()?;
        }
        let rollup = summary_rollup(set.as_ref());
        let helpers = helper_views(set.as_ref());
        Ok(Self {
            set,
            rollup,
            helpers,
        })
    }

    pub fn as_set(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.set.as_ref()
    }

    pub fn root_summary(&self) -> Option<&r2ssa::FunctionSemanticSummary> {
        let set = self.set.as_ref()?;
        let root = set.root?;
        set.summaries.get(&root)
    }

    pub fn diagnostics(&self) -> Option<&r2ssa::InterprocSummaryDiagnostics> {
        self.set.as_ref().map(|set| &set.diagnostics)
    }

    pub fn helper_summary_for_name(&self, name: &str) -> Option<&r2ssa::FunctionSemanticSummary> {
        let normalized = name.trim().to_ascii_lowercase();
        self.set.as_ref()?.summaries.values().find(|summary| {
            summary
                .name
                .as_deref()
                .is_some_and(|summary_name| summary_name.trim().to_ascii_lowercase() == normalized)
        })
    }

    pub fn helper_view_for_name(&self, name: &str) -> Option<&SummaryHelperView> {
        let normalized = name.trim().to_ascii_lowercase();
        self.helpers.iter().find(|summary| {
            summary
                .name
                .as_deref()
                .is_some_and(|summary_name| summary_name.trim().to_ascii_lowercase() == normalized)
        })
    }

    pub fn out_param_indices(&self) -> Vec<usize> {
        out_param_indices_from_facts(
            self.rollup
                .as_ref()
                .map(|rollup| rollup.out_param_facts.as_slice())
                .unwrap_or(&[]),
        )
    }

    pub fn pointer_param_indices(&self) -> &[usize] {
        self.rollup
            .as_ref()
            .map(|rollup| rollup.pointer_param_indices.as_slice())
            .unwrap_or(&[])
    }
}

/// Advisory function-analysis report.
///
/// This detached view is useful for diagnostics and rendering at report
/// boundaries. It may retain opaque semantic or interprocedural evidence
/// owners, but it does not itself require one exact prepared SSA source and
/// cannot be promoted into source-dependent certification.
#[derive(Debug, Clone, Default)]
pub struct FunctionFacts {
    types: FunctionTypeFacts,
    semantics: Option<r2sym::SemanticArtifact>,
    interproc_summary: Option<r2ssa::PreparedInterprocSummarySet>,
    decompile_route: Option<DecompileRouteFacts>,
    input_quality: Option<FunctionInputQualityFacts>,
    callee_resolution: CalleeResolutionFacts,
    /// Spellings radare2 already holds for the addresses this function
    /// touches. Rendering reads them; nothing that decides behaviour does.
    display_names: crate::DisplayNames,
    callsites: FunctionCallsiteFacts,
    call_results: FunctionCallResultFacts,
    call_render: FunctionCallRenderFacts,
    control: FunctionControlFacts,
    render: FunctionRenderFacts,
    assumptions: r2ssa::AssumptionSet,
    plans: AnalysisPlans,
    summary_view: InterprocSummaryView,
    diagnostics: Vec<String>,
    assumption_usage: r2ssa::AssumptionUsageReport,
}

/// Opaque source-owned function facts.
///
/// The exact prepared SSA allocation is retained alongside its advisory
/// report. There is deliberately no public promotion or parts constructor:
/// authoritative instances are sealed only by source-owned writeback after
/// all semantic, interprocedural, assumption, and machine-context checks pass.
#[derive(Debug, Clone)]
pub struct SourceOwnedFunctionFacts {
    source: Arc<r2ssa::SsaArtifact>,
    report: FunctionFacts,
    evidence_types: crate::EvidenceTypes,
    _callee_signatures: BTreeMap<u64, SourceOwnedCalleeSignature>,
}

/// One C signature derived from the exact retained body that owns it.
///
/// Construction is crate-private: callers may transport this certificate, but
/// cannot pair an arbitrary signature with an SSA body. The retained function
/// interface also lets a caller prove that this is the same physical contract
/// `r2ssa` admitted at its call site before consuming the logical C types.
#[derive(Debug, Clone)]
pub struct SourceOwnedCalleeSignature {
    source: Arc<r2ssa::SsaArtifact>,
    interface: r2ssa::SourceFunctionInterface,
    signature: crate::FunctionType,
}

impl SourceOwnedCalleeSignature {
    pub(crate) fn new(
        source: Arc<r2ssa::SsaArtifact>,
        signature: crate::FunctionType,
    ) -> Option<Self> {
        let interface = source.machine_context().function_interface()?.clone();
        function_type_matches_source_interface(
            &signature,
            &interface,
            source
                .machine_context()
                .memory_model()
                .default_address_bits(),
        )
        .then_some(Self {
            source,
            interface,
            signature,
        })
    }

    pub(crate) fn address(&self) -> u64 {
        self.source.function().entry
    }
}

impl SourceOwnedFunctionFacts {
    #[cfg(test)]
    pub(crate) fn seal(source: Arc<r2ssa::SsaArtifact>, report: FunctionFacts) -> Option<Self> {
        Self::seal_with_callee_signatures(source, report, BTreeMap::new())
    }

    pub(crate) fn seal_with_callee_signatures(
        source: Arc<r2ssa::SsaArtifact>,
        mut report: FunctionFacts,
        callee_signatures: BTreeMap<u64, SourceOwnedCalleeSignature>,
    ) -> Option<Self> {
        // Canonicalization is part of sealing. Runtime consumers must observe
        // this exact report and may not clone then normalize it independently.
        report.canonicalize_type_facts();
        if report.assumptions() != &source.facts().assumptions
            || report
                .semantic_artifact()
                .is_some_and(|artifact| !artifact.shares_artifact(source.as_ref()))
            || report
                .prepared_interproc_summary()
                .is_some_and(|summary| !summary.matches_root(&source))
        {
            return None;
        }
        // Source-owned facts are authoritative only when every source-dependent
        // projection is exactly what this retained SSA artifact produces. Both
        // construction and consumers previously read `report`, so a stale
        // detached render/call/control row could validate against itself. Build
        // the projection again from the retained source and the final canonical
        // type payload, then require exact equality before sealing.
        let mut expected = report.clone();
        Self::rebuild_source_owned_decompile_evidence(source.as_ref(), &mut expected);
        expected.apply_source_owned_callee_signatures(source.as_ref(), &callee_signatures);
        if report.types != expected.types
            || report.callee_resolution != expected.callee_resolution
            || report.callsites != expected.callsites
            || report.call_results != expected.call_results
            || report.call_render != expected.call_render
            || report.control != expected.control
            || report.render != expected.render
        {
            return None;
        }
        let ptr_bits = source
            .machine_context()
            .memory_model()
            .default_address_bits();
        let evidence_types =
            crate::solve_evidence_types(source.as_ref(), &report.callsite_signatures(), ptr_bits);
        Some(Self {
            source,
            report,
            evidence_types,
            _callee_signatures: callee_signatures,
        })
    }

    pub fn source(&self) -> &r2ssa::SsaArtifact {
        self.source.as_ref()
    }

    pub fn shared_source(&self) -> Arc<r2ssa::SsaArtifact> {
        Arc::clone(&self.source)
    }

    pub fn shares_source(&self, source: &Arc<r2ssa::SsaArtifact>) -> bool {
        Arc::ptr_eq(&self.source, source)
    }

    pub fn report(&self) -> &FunctionFacts {
        &self.report
    }

    /// Exact ValueId/ObjectId-keyed type solution for the retained source.
    pub fn evidence_types(&self) -> &crate::EvidenceTypes {
        &self.evidence_types
    }

    pub(crate) fn stamp_report_decompile_route(
        report: &mut FunctionFacts,
        kind: DecompileRouteKind,
        reason: impl Into<String>,
        fallback_comment: Option<String>,
    ) -> bool {
        let reason = reason.into();
        let reason = if reason.trim().is_empty() {
            "source-owned decompile route".to_string()
        } else {
            reason
        };
        let compatible = match kind {
            DecompileRouteKind::Standard | DecompileRouteKind::FallbackComment => true,
            DecompileRouteKind::VmSummary => report
                .semantic_report()
                .and_then(r2sym::SemanticArtifactReport::vm_body)
                .is_some(),
            DecompileRouteKind::StructuredWorker => report
                .semantic_report()
                .and_then(r2sym::SemanticArtifactReport::native_body)
                .is_some_and(|body| !body.regions.is_empty()),
            DecompileRouteKind::SummaryIslands => report
                .semantic_report()
                .and_then(r2sym::SemanticArtifactReport::native_body)
                .is_some_and(r2sym::NativeArtifactBody::has_summary_islands),
            DecompileRouteKind::LinearWorker => report
                .semantic_report()
                .and_then(r2sym::SemanticArtifactReport::native_body)
                .is_some_and(|body| !body.summary.worker_summaries.is_empty()),
        };
        let (kind, reason, fallback_comment) = if compatible {
            (kind, reason, fallback_comment)
        } else {
            let reason = format!(
                "source-owned route refused: {:?} is incompatible with retained report",
                kind
            );
            (
                DecompileRouteKind::FallbackComment,
                reason.clone(),
                Some(format!("/* {reason} */")),
            )
        };
        let use_prepared_semantic_view =
            kind == DecompileRouteKind::Standard && report.render().is_some();
        report.set_decompile_route(Some(DecompileRouteFacts {
            kind,
            reason: Some(reason),
            fallback_comment: (kind == DecompileRouteKind::FallbackComment)
                .then_some(fallback_comment)
                .flatten(),
            use_prepared_semantic_view,
        }));
        compatible
    }

    /// Attach the decompile evidence the source can support.
    ///
    /// Parameter-slot resolution needs a coherent ABI. When the source does not
    /// carry one there are no parameter slots to resolve, so the steps keyed on
    /// them have nothing to do; every other piece of evidence is still valid and
    /// is still attached. Returns the number of parameter declarations that
    /// changed and whether the return declaration changed in the final signature.
    #[cfg(test)]
    pub(crate) fn enrich_report_from_source_for_decompile(
        source: &r2ssa::SsaArtifact,
        report: &mut FunctionFacts,
    ) -> (usize, bool) {
        Self::enrich_report_from_source_with_callee_signatures(source, report, &BTreeMap::new())
    }

    pub(crate) fn enrich_report_from_source_with_callee_signatures(
        source: &r2ssa::SsaArtifact,
        report: &mut FunctionFacts,
        callee_signatures: &BTreeMap<u64, SourceOwnedCalleeSignature>,
    ) -> (usize, bool) {
        let prior_signature = report.types.merged_signature.clone();
        let mut enriched = report.clone();
        let mut usage = source.facts().assumption_usage.clone();
        usage.extend(enriched.assumption_usage());
        enriched.assumption_usage = usage;
        enriched.display_names.absorb(source.display_names());
        Self::rebuild_source_owned_decompile_evidence(source, &mut enriched);
        enriched.apply_source_owned_callee_signatures(source, callee_signatures);
        let ptr_bits = source
            .machine_context()
            .memory_model()
            .default_address_bits();
        enriched.apply_certified_call_argument_type_constraints(ptr_bits);
        enriched.apply_recovered_evidence_types(source, ptr_bits);
        // Exact immutable interface evidence outranks advisory propagation.
        // Apply it after recovered call evidence so the latter cannot rewrite
        // a declared signedness or logical projection through a weak scalar.
        enriched.apply_exact_source_return_type(source);
        // Type constraints may change advisory member/carrier types. Rebuild
        // once more so the sealed render projection is a pure function of the
        // final type facts and the exact retained source.
        Self::rebuild_source_owned_decompile_evidence(source, &mut enriched);
        enriched.apply_source_owned_callee_signatures(source, callee_signatures);
        let final_signature = enriched.types.merged_signature.as_ref();
        let changed_parameters = final_signature.map_or(0, |signature| {
            signature
                .params
                .iter()
                .enumerate()
                .filter(|(slot, parameter)| {
                    prior_signature
                        .as_ref()
                        .and_then(|signature| signature.params.get(*slot))
                        .and_then(|parameter| parameter.ty.as_ref())
                        != parameter.ty.as_ref()
                })
                .count()
        });
        let return_type_changed = prior_signature
            .as_ref()
            .and_then(|signature| signature.ret_type.as_ref())
            != final_signature.and_then(|signature| signature.ret_type.as_ref());
        *report = enriched;
        (changed_parameters, return_type_changed)
    }

    fn rebuild_source_owned_decompile_evidence(
        source: &r2ssa::SsaArtifact,
        report: &mut FunctionFacts,
    ) {
        let param_slots = exact_source_param_slot_resolver(source);
        report.attach_prepared_decompile_evidence(source);
        if let Some(param_slots) = param_slots.as_ref() {
            report.populate_certified_parameter_exprs(source, param_slots);
        }
        report.normalize_field_certificates_from_external_layout();
        if let Some(param_slots) = param_slots.as_ref() {
            report.populate_member_access_render_facts_from_field_certificates(source, param_slots);
        }
        report.populate_certified_loop_carrier_types();
        if let Some(param_slots) = param_slots.as_ref() {
            report.populate_array_access_render_facts_from_scalar_candidates(source, param_slots);
        }
    }
}

/// The logical return type licensed by the exact source interface and every
/// certified machine return boundary.
///
/// This is independent of whether advisory type recovery happened to create a
/// whole [`FunctionSignatureSpec`]. In particular, a tail-only function has no
/// `SSAOp::Return` from which the decompiler could infer a type, while its exact
/// tail-call boundary still proves the carrier returned on the caller's behalf.
pub fn exact_source_return_type(source: &r2ssa::SsaArtifact) -> Option<CTypeLike> {
    let context = source.machine_context();
    let abi = context.abi_model();
    let memory = context.memory_model();
    if !abi.is_available() || !abi.is_coherent() || !memory.is_available() || !memory.is_coherent()
    {
        return None;
    }
    let interface = context.function_interface()?;
    let r2ssa::SourceFunctionReturn::Register { storage } = interface.return_kind() else {
        return None;
    };
    if storage.space != r2ssa::CanonicalStorageSpace::Register || storage.size == 0 {
        return None;
    }
    let logical = interface.return_logical_value()?;
    let graph = interface.type_graph()?;
    let source_type = graph
        .types()
        .get(usize::try_from(logical.type_id()).ok()?)
        .filter(|source_type| source_type.id() == logical.type_id())?;
    let projection = logical.carrier();
    let storage_bits = u64::from(storage.size).checked_mul(8)?;
    if projection.offset_bits() != 0
        || projection.size_bits() == 0
        || projection.size_bits() != source_type.size_bits()
        || projection.size_bits() % 8 != 0
        || projection.size_bits() > storage_bits
    {
        return None;
    }
    let logical_width = match projection.kind() {
        r2ssa::SourceCarrierKind::Full if projection.size_bits() == storage_bits => storage.size,
        r2ssa::SourceCarrierKind::LowBits
            if projection.size_bits() < storage_bits
                && matches!(
                    source_type.kind(),
                    r2ssa::SourceTypeKind::SignedInteger | r2ssa::SourceTypeKind::UnsignedInteger
                ) =>
        {
            u32::try_from(projection.size_bits() / 8).ok()?
        }
        _ => return None,
    };
    let expected_carrier = r2ssa::ReturnCarrier::Register { storage };
    let mut return_count = 0usize;
    for &block_addr in source.function().block_addrs() {
        let block = source.function().get_block(block_addr)?;
        for (op_index, op) in block.ops.iter().enumerate() {
            if !matches!(op, r2ssa::SSAOp::Return { .. }) {
                continue;
            }
            return_count = return_count.checked_add(1)?;
            let certificate = source.return_certificate_for_op(block_addr, op_index)?;
            if !exact_return_certificate_matches(
                certificate,
                logical,
                logical_width,
                &expected_carrier,
            ) {
                return None;
            }
        }
    }
    let mut tail_return_count = 0usize;
    for call_site in source
        .facts()
        .call_sites
        .by_id
        .values()
        .filter(|call_site| call_site.transfer == r2ssa::CallSiteTransfer::TailCall)
    {
        let certificate = source.certificates().callsites.get(&call_site.id)?;
        let boundary = source.facts().boundaries.calls.get(&call_site.id)?;
        if !exact_tail_return_certificate_matches(call_site, certificate, boundary, storage) {
            return None;
        }
        tail_return_count = tail_return_count.checked_add(1)?;
    }
    let certified_tail_return_count = source
        .certificates()
        .callsites
        .values()
        .filter(|certificate| certificate.transfer == r2ssa::CallSiteTransfer::TailCall)
        .count();
    if return_count + tail_return_count == 0
        || source.certificates().returns.len() != return_count
        || source.certificates().returns_by_inst.len() != return_count
        || certified_tail_return_count != tail_return_count
    {
        return None;
    }

    crate::writeback::source_type_like(graph, logical.type_id(), &mut BTreeSet::new())
}

fn exact_return_certificate_matches(
    certificate: &r2ssa::ReturnValueCertificate,
    logical: r2ssa::SourceLogicalValue,
    logical_width: u32,
    expected_carrier: &r2ssa::ReturnCarrier,
) -> bool {
    certificate.source_logical_value == Some(logical)
        && certificate.width == logical_width
        && certificate.carrier.as_ref() == Some(expected_carrier)
}

fn exact_tail_return_certificate_matches(
    call_site: &r2ssa::CallSiteFact,
    certificate: &r2ssa::CallsiteCertificate,
    boundary: &r2ssa::SourceCallBoundaryFact,
    expected_storage: r2ssa::CanonicalStorageId,
) -> bool {
    call_site.transfer == r2ssa::CallSiteTransfer::TailCall
        && call_site.raw_identity.is_some()
        && certificate.transfer == r2ssa::CallSiteTransfer::TailCall
        && certificate.call_site == call_site.id
        && certificate.at == call_site.at
        && certificate.target == call_site.target
        && boundary.call_site == call_site.id
        && boundary.at == call_site.at
        && boundary.complete
        && boundary.result_kind
            == Some(r2ssa::SourceCallResult::Register {
                storage: expected_storage,
            })
}

fn exact_source_param_slot_resolver(source: &r2ssa::SsaArtifact) -> Option<ParamSlotResolver> {
    let context = source.machine_context();
    let interface = context.function_interface()?;
    let abi = context.abi_model();
    if !abi.is_available() {
        return None;
    }
    let mut resolver = ParamSlotResolver::default();
    for (index, parameter) in &source.facts().boundaries.parameters {
        let slot = usize::try_from(*index).ok()?;
        let source_parameter = interface
            .parameters()
            .iter()
            .find(|candidate| candidate.index() == *index)?;
        let abi_slot = abi
            .argument_registers()
            .iter()
            .find(|candidate| candidate.index() == *index)?;
        let graph_value = source.graph().value(parameter.value)?;
        if parameter.index != *index
            || parameter.abi_storage != source_parameter.storage()
            || parameter.abi_storage != abi_slot.storage()
            || graph_value.canonical_storage != Some(parameter.graph_storage)
            || graph_value.var.size != parameter.graph_storage.size
            || graph_value.var.version != 0
            || source.graph().def_inst(parameter.value).is_some()
            || resolver
                .slots_by_value
                .insert(parameter.value, slot)
                .is_some()
        {
            return None;
        }
    }
    Some(resolver)
}

impl FunctionFacts {
    pub fn new(types: FunctionTypeFacts, semantics: Option<r2sym::SemanticArtifact>) -> Self {
        let plans =
            AnalysisPlans::from_semantics(semantics.as_ref().map(r2sym::SemanticArtifact::report));
        Self {
            types,
            semantics,
            interproc_summary: None,
            decompile_route: None,
            input_quality: None,
            callee_resolution: CalleeResolutionFacts::default(),
            display_names: crate::DisplayNames::default(),
            callsites: FunctionCallsiteFacts::default(),
            call_results: FunctionCallResultFacts::default(),
            call_render: FunctionCallRenderFacts::default(),
            control: FunctionControlFacts::default(),
            render: FunctionRenderFacts::default(),
            assumptions: r2ssa::AssumptionSet::default(),
            plans,
            summary_view: InterprocSummaryView::default(),
            diagnostics: Vec::new(),
            assumption_usage: r2ssa::AssumptionUsageReport::default(),
        }
    }

    pub fn with_assumptions(mut self, assumptions: r2ssa::AssumptionSet) -> Self {
        self.assumptions = assumptions;
        self
    }

    pub(crate) fn with_summary_view(mut self, summary_view: InterprocSummaryView) -> Self {
        self.interproc_summary = None;
        self.summary_view = summary_view;
        self
    }

    pub(crate) fn with_prepared_interproc_summary(
        mut self,
        summary: r2ssa::PreparedInterprocSummarySet,
    ) -> Self {
        if self.semantics.as_ref().is_some_and(|semantics| {
            !std::sync::Arc::ptr_eq(&semantics.shared_prepared(), summary.root())
        }) {
            return self;
        }
        let Ok(summary_view) = InterprocSummaryView::new(Some(summary.report().clone())) else {
            self.summary_view = InterprocSummaryView::default();
            self.interproc_summary = None;
            return self;
        };
        self.summary_view = summary_view;
        self.interproc_summary = Some(summary);
        self
    }

    pub fn with_diagnostics<I>(mut self, diagnostics: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        self.diagnostics = diagnostics.into_iter().collect();
        self
    }

    pub fn with_assumption_usage(mut self, usage: r2ssa::AssumptionUsageReport) -> Self {
        self.assumption_usage = usage;
        self
    }

    pub fn merge_assumption_usage(&mut self, usage: &r2ssa::AssumptionUsageReport) {
        self.assumption_usage.extend(usage);
    }

    pub fn with_decompile_route(mut self, route: DecompileRouteFacts) -> Self {
        self.decompile_route = Some(route);
        self
    }

    pub fn with_input_quality(mut self, input_quality: FunctionInputQualityFacts) -> Self {
        self.input_quality = Some(input_quality);
        self
    }

    pub fn set_input_quality(&mut self, input_quality: Option<FunctionInputQualityFacts>) {
        self.input_quality = input_quality;
    }

    pub fn input_quality(&self) -> Option<&FunctionInputQualityFacts> {
        self.input_quality.as_ref()
    }

    pub fn with_callee_resolution(mut self, callee_resolution: CalleeResolutionFacts) -> Self {
        self.callee_resolution = callee_resolution;
        self
    }

    pub fn set_callee_resolution(&mut self, callee_resolution: CalleeResolutionFacts) {
        self.callee_resolution = callee_resolution;
    }

    pub fn callee_resolution(&self) -> Option<&CalleeResolutionFacts> {
        (!self.callee_resolution.is_empty()).then_some(&self.callee_resolution)
    }

    pub fn with_callsites(mut self, callsites: FunctionCallsiteFacts) -> Self {
        self.callsites = callsites;
        self
    }

    pub fn set_callsites(&mut self, callsites: FunctionCallsiteFacts) {
        self.callsites = callsites;
    }

    pub fn callsites(&self) -> Option<&FunctionCallsiteFacts> {
        (!self.callsites.is_empty()).then_some(&self.callsites)
    }

    fn apply_source_owned_callee_signatures(
        &mut self,
        source: &r2ssa::SsaArtifact,
        signatures: &BTreeMap<u64, SourceOwnedCalleeSignature>,
    ) {
        for arguments in self.callsites.by_callsite.values_mut() {
            let Some(target) = arguments.direct_target else {
                continue;
            };
            let Some(signature) = signatures.get(&target) else {
                continue;
            };
            let same_interface = source
                .machine_context()
                .call_site_interface(arguments.call_site_id)
                .and_then(r2ssa::SourceCallSiteInterface::exact_callee_interface)
                .is_some_and(|interface| interface == &signature.interface);
            if same_interface && signature.address() == target {
                let mut logical_signature = signature.signature.clone();
                logical_signature.variadic = arguments.variadic;
                arguments.callee_signature = Some(logical_signature);
            }
        }
    }

    pub fn with_call_results(mut self, call_results: FunctionCallResultFacts) -> Self {
        self.call_results = call_results;
        self
    }

    pub fn set_call_results(&mut self, call_results: FunctionCallResultFacts) {
        self.call_results = call_results;
    }

    pub fn call_results(&self) -> Option<&FunctionCallResultFacts> {
        (!self.call_results.is_empty()).then_some(&self.call_results)
    }

    pub fn with_call_render(mut self, call_render: FunctionCallRenderFacts) -> Self {
        self.call_render = call_render;
        self
    }

    pub fn set_call_render(&mut self, call_render: FunctionCallRenderFacts) {
        self.call_render = call_render;
    }

    pub fn call_render(&self) -> Option<&FunctionCallRenderFacts> {
        (!self.call_render.is_empty()).then_some(&self.call_render)
    }

    pub fn with_control(mut self, control: FunctionControlFacts) -> Self {
        self.control = control;
        self
    }

    pub fn set_control(&mut self, control: FunctionControlFacts) {
        self.control = control;
    }

    pub fn control(&self) -> Option<&FunctionControlFacts> {
        (!self.control.is_empty()).then_some(&self.control)
    }

    #[cfg(test)]
    fn with_render(mut self, render: FunctionRenderFacts) -> Self {
        self.render = render;
        self
    }

    pub fn render(&self) -> Option<&FunctionRenderFacts> {
        (!self.render.is_empty()).then_some(&self.render)
    }

    pub fn render_facts(&self) -> &FunctionRenderFacts {
        &self.render
    }

    /// Spellings for the addresses this function touches.
    ///
    /// Rendering asks this what to print. Nothing that decides what a call
    /// does, which route to take, or what type something has may consult it:
    /// a name is presentation, and treating it as evidence is how a decompiler
    /// starts inventing semantics from symbol strings.
    pub fn display_names(&self) -> &crate::DisplayNames {
        &self.display_names
    }

    /// Attach the spellings radare2 already holds.
    pub fn set_display_names(&mut self, names: crate::DisplayNames) {
        self.display_names = names;
    }

    pub fn control_facts(&self) -> &FunctionControlFacts {
        &self.control
    }

    pub fn authorized_stack_slot_owner_render(
        &self,
        object: r2ssa::ObjectId,
        offset: i64,
        name: &str,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let name = name.trim();
        if name.is_empty() {
            return None;
        }
        let render_offset = self.render.stack_slot_offset(object)?;
        if render_offset != offset || !self.stack_owner_name_is_renderable(offset, name) {
            return None;
        }
        Some(StackSlotOwnerRenderAuthorization {
            object,
            offset,
            name: name.to_string(),
        })
    }

    pub fn authorized_stack_slot_owner_render_by_offset(
        &self,
        offset: i64,
        name: &str,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let mut matching_objects = self
            .render
            .stack_slots()
            .filter_map(|(object, _, slot_offset, _)| (slot_offset == offset).then_some(object));
        let object = matching_objects.next()?;
        if matching_objects.next().is_some() {
            return None;
        }
        self.authorized_stack_slot_owner_render(object, offset, name)
    }

    pub fn authorized_stack_param_owner_render(
        &self,
        object: r2ssa::ObjectId,
        offset: i64,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let render_offset = self.render.stack_slot_offset(object)?;
        if render_offset != offset {
            return None;
        }
        if let Some(name) = self.stack_param_owner_name_for_offset(offset) {
            return self.authorized_stack_slot_owner_render(object, offset, &name);
        }
        None
    }

    fn stack_param_owner_name_for_offset(&self, offset: i64) -> Option<String> {
        let mut candidate = None;
        for (slot_key, slot) in &self.types.stack_slots {
            if stack_slot_matches_offset(slot_key, offset)
                && matches!(
                    slot.role,
                    ExternalStackSlotRole::StackArg | ExternalStackSlotRole::ParamHome
                )
            {
                if let Some(name) =
                    indexed_param_home_name(self.types.merged_signature.as_ref(), slot)
                {
                    remember_stack_param_owner_name(&mut candidate, name)?;
                    continue;
                }
                if let Some(name) = slot
                    .param_name
                    .as_ref()
                    .filter(|name| !name.trim().is_empty())
                    .filter(|name| {
                        slot.ty.as_ref().is_some_and(stack_owner_type_is_renderable)
                            || (matches!(slot.role, ExternalStackSlotRole::ParamHome)
                                && signature_param_name_type_is_renderable(
                                    self.types.merged_signature.as_ref(),
                                    name,
                                ))
                    })
                {
                    remember_stack_param_owner_name(&mut candidate, name)?;
                    continue;
                }
                if !slot.name.trim().is_empty() {
                    remember_stack_param_owner_name(&mut candidate, &slot.name)?;
                }
            }
        }
        if candidate.is_some() {
            return candidate;
        }

        for binding in &self.types.visible_bindings {
            let Some(slot) = binding.stack_slot.as_ref() else {
                continue;
            };
            if stack_slot_matches_offset(slot, offset)
                && matches!(binding.kind, VisibleBindingKind::Param)
                && binding
                    .ty
                    .as_ref()
                    .is_some_and(stack_owner_type_is_renderable)
                && !binding.name.trim().is_empty()
            {
                remember_stack_param_owner_name(&mut candidate, &binding.name)?;
            }
        }
        candidate
    }

    fn stack_owner_name_is_renderable(&self, offset: i64, name: &str) -> bool {
        self.types.visible_bindings.iter().any(|binding| {
            let Some(slot) = binding.stack_slot.as_ref() else {
                return false;
            };
            binding.name.eq_ignore_ascii_case(name)
                && stack_slot_matches_offset(slot, offset)
                && binding
                    .ty
                    .as_ref()
                    .is_some_and(stack_owner_type_is_renderable)
                && visible_stack_binding_kind_is_renderable(&binding.kind)
        }) || self.types.stack_slots.iter().any(|(slot_key, slot)| {
            if !stack_slot_matches_offset(slot_key, offset) {
                return false;
            }
            if let Some(canonical_name) =
                indexed_param_home_name(self.types.merged_signature.as_ref(), slot)
            {
                return canonical_name.eq_ignore_ascii_case(name);
            }
            (slot.name.eq_ignore_ascii_case(name)
                || (matches!(
                    slot.role,
                    ExternalStackSlotRole::StackArg | ExternalStackSlotRole::ParamHome
                ) && slot
                    .param_name
                    .as_ref()
                    .is_some_and(|param_name| param_name.eq_ignore_ascii_case(name))))
                && (slot.ty.as_ref().is_some_and(stack_owner_type_is_renderable)
                    || (matches!(slot.role, ExternalStackSlotRole::ParamHome)
                        && slot.param_name.as_ref().is_some_and(|param_name| {
                            param_name.eq_ignore_ascii_case(name)
                                && signature_param_name_type_is_renderable(
                                    self.types.merged_signature.as_ref(),
                                    param_name,
                                )
                        })))
                && (external_stack_slot_role_is_renderable(slot.role)
                    || (matches!(slot.role, ExternalStackSlotRole::ParamHome)
                        && slot
                            .param_name
                            .as_ref()
                            .is_some_and(|param_name| param_name.eq_ignore_ascii_case(name))))
        })
    }

    pub fn authorized_recovered_stack_slot_owner_render(
        &self,
        object: r2ssa::ObjectId,
        offset: i64,
        name: &str,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let name = name.trim();
        if !recovered_stack_owner_name_is_renderable(name) {
            return None;
        }
        let render_offset = self.render.stack_slot_offset(object)?;
        if render_offset != offset {
            return None;
        }
        Some(StackSlotOwnerRenderAuthorization {
            object,
            offset,
            name: name.to_string(),
        })
    }

    fn set_decompile_route(&mut self, route: Option<DecompileRouteFacts>) {
        self.decompile_route = route;
    }

    pub fn decompile_route(&self) -> Option<&DecompileRouteFacts> {
        self.decompile_route.as_ref()
    }

    pub fn decompile_fallback_comment(&self) -> Option<&str> {
        self.decompile_route
            .as_ref()
            .filter(|route| route.kind == DecompileRouteKind::FallbackComment)
            .and_then(|route| {
                route
                    .fallback_comment
                    .as_deref()
                    .or(route.reason.as_deref())
            })
    }

    pub(crate) fn set_semantics(&mut self, semantics: Option<r2sym::SemanticArtifact>) {
        if semantics.as_ref().is_some_and(|semantics| {
            self.interproc_summary.as_ref().is_some_and(|summary| {
                !std::sync::Arc::ptr_eq(&semantics.shared_prepared(), summary.root())
            })
        }) {
            self.interproc_summary = None;
            self.summary_view = InterprocSummaryView::default();
        }
        self.semantics = semantics;
        self.refresh_plans();
    }

    pub fn refresh_plans(&mut self) {
        self.plans = AnalysisPlans::from_semantics(
            self.semantics.as_ref().map(r2sym::SemanticArtifact::report),
        );
    }

    pub fn canonicalize_type_facts(&mut self) {
        self.types = std::mem::take(&mut self.types).canonicalized();
        self.refresh_plans();
    }

    pub fn replace_type_facts(&mut self, types: FunctionTypeFacts) {
        self.types = types.canonicalized();
        self.refresh_plans();
    }

    pub fn normalize_field_certificates_from_external_layout(&mut self) {
        let Some(signature) = self.types.merged_signature.as_ref() else {
            return;
        };
        let type_db = &self.types.external_type_db;
        if type_db.structs.is_empty() {
            return;
        }

        for cert in &mut self.types.field_access_certificates {
            let Some(param) = signature.params.get(cert.slot) else {
                continue;
            };
            let Some(struct_name) = struct_name_from_pointer_type(param.ty.as_ref()) else {
                continue;
            };
            let key = normalize_external_type_name(struct_name).to_ascii_lowercase();
            let Some(field) = type_db
                .structs
                .get(&key)
                .and_then(|structure| structure.fields.get(&cert.field_offset))
            else {
                continue;
            };
            cert.field_name = field.name.clone();
            if cert.field_type.is_none() {
                cert.field_type = field.ty.clone();
            }
        }
    }

    fn populate_member_access_render_facts_from_field_certificates(
        &mut self,
        prepared: &r2ssa::SsaArtifact,
        param_slots: &ParamSlotResolver,
    ) {
        if self.types.field_access_certificates.is_empty() {
            return;
        }

        let mut member_facts = Vec::new();
        for memory in self.render.memory_accesses() {
            if memory.width == 0 {
                continue;
            }
            let Some(field_offset) = prepared_memory_access_field_offset(prepared, memory) else {
                continue;
            };
            let param_slot = prepared_memory_access_param_slot(prepared, memory, param_slots);
            let ptr_bits = prepared_memory_access_ptr_bits(prepared, memory);
            member_facts.extend(self.member_render_facts_for_memory(
                memory,
                field_offset,
                ptr_bits,
                param_slot,
            ));
        }

        for candidate in self.types.scalar_array_render_candidates.iter().copied() {
            if candidate.access_width == 0
                || !self.scalar_array_render_candidate_has_array_certificate(candidate)
            {
                continue;
            }
            let key = (candidate.block_addr, candidate.op_index, candidate.is_write);
            let Some(effect_ids) = self.render.memory_effects_by_op.get(&key) else {
                continue;
            };
            for effect_id in effect_ids {
                let Some(memory) = self
                    .render
                    .certified_effect(*effect_id)
                    .and_then(CertifiedEffect::memory_fact)
                else {
                    continue;
                };
                if memory.block_addr != candidate.block_addr
                    || memory.op_index != candidate.op_index
                    || memory.is_write != candidate.is_write
                    || memory.width == 0
                    || memory.width != candidate.access_width
                {
                    continue;
                }
                if self
                    .certified_scalar_array_identity(prepared, memory, candidate)
                    .is_none()
                {
                    continue;
                }
                let ptr_bits = prepared_memory_access_ptr_bits(prepared, memory);
                member_facts.extend(self.member_render_facts_for_memory(
                    memory,
                    candidate.field_offset,
                    ptr_bits,
                    Some(candidate.slot),
                ));
            }
        }

        for fact in member_facts {
            let key = (fact.block_addr, fact.op_index, fact.is_write);
            let facts = self.render.member_accesses_by_op.entry(key).or_default();
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }

        for facts in self.render.member_accesses_by_op.values_mut() {
            facts.sort_by(|a, b| {
                (
                    a.block_addr,
                    a.op_index,
                    a.is_write,
                    a.field_offset,
                    a.access_width,
                    a.field_name.as_str(),
                    a.access,
                )
                    .cmp(&(
                        b.block_addr,
                        b.op_index,
                        b.is_write,
                        b.field_offset,
                        b.access_width,
                        b.field_name.as_str(),
                        b.access,
                    ))
            });
        }
    }

    fn member_render_facts_for_memory(
        &self,
        memory: &MemoryAccessRenderFact,
        field_offset: u64,
        ptr_bits: u32,
        param_slot: Option<usize>,
    ) -> Vec<MemberAccessRenderFact> {
        self.types
            .field_access_certificates
            .iter()
            .filter(|cert| {
                param_slot == Some(cert.slot)
                    && cert.field_offset == field_offset
                    && field_certificate_width_matches(cert, memory.width, ptr_bits)
            })
            .map(|cert| MemberAccessRenderFact {
                access: memory.access,
                block_addr: memory.block_addr,
                op_index: memory.op_index,
                object: memory.object,
                is_write: memory.is_write,
                field_offset,
                field_name: cert.field_name.clone(),
                field_type: cert
                    .field_type
                    .as_deref()
                    .and_then(|ty| parse_c_type_like(ty, ptr_bits)),
                access_width: memory.width,
            })
            .collect()
    }

    fn populate_array_access_render_facts_from_scalar_candidates(
        &mut self,
        prepared: &r2ssa::SsaArtifact,
        _param_slots: &ParamSlotResolver,
    ) {
        if self.types.scalar_array_render_candidates.is_empty() {
            return;
        }

        for candidate in self.types.scalar_array_render_candidates.iter().copied() {
            if candidate.element_stride == 0
                || candidate.access_width == 0
                || !self.scalar_array_render_candidate_has_array_certificate(candidate)
            {
                continue;
            }
            let key = (candidate.block_addr, candidate.op_index, candidate.is_write);
            let Some(effect_ids) = self.render.memory_effects_by_op.get(&key) else {
                continue;
            };
            let effect_ids = effect_ids.clone();
            for effect_id in effect_ids {
                let Some(memory) = self
                    .render
                    .certified_effect(effect_id)
                    .and_then(CertifiedEffect::memory_fact)
                else {
                    continue;
                };
                if memory.block_addr != candidate.block_addr
                    || memory.op_index != candidate.op_index
                    || memory.is_write != candidate.is_write
                    || memory.width == 0
                    || memory.width != candidate.access_width
                {
                    continue;
                }
                let Some((base, index)) =
                    self.certified_scalar_array_identity(prepared, memory, candidate)
                else {
                    continue;
                };
                let fact = ArrayAccessRenderFact {
                    access: memory.access,
                    block_addr: memory.block_addr,
                    op_index: memory.op_index,
                    object: memory.object,
                    is_write: memory.is_write,
                    field_offset: candidate.field_offset,
                    element_stride: candidate.element_stride,
                    access_width: memory.width,
                    base: Some(base),
                    index: Some(index),
                };
                let facts = self.render.array_accesses_by_op.entry(key).or_default();
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
        }

        for facts in self.render.array_accesses_by_op.values_mut() {
            facts.sort_by_key(|fact| {
                (
                    fact.block_addr,
                    fact.op_index,
                    fact.is_write,
                    fact.field_offset,
                    fact.element_stride,
                    fact.access_width,
                    fact.access,
                    fact.object,
                    fact.base,
                    fact.index,
                )
            });
        }
    }

    fn scalar_array_render_candidate_has_array_certificate(
        &self,
        candidate: crate::facts::ScalarArrayRenderCandidate,
    ) -> bool {
        self.types.array_index_certificates.iter().any(|cert| {
            cert.slot == candidate.slot
                && cert.field_offset == candidate.field_offset
                && cert.element_stride == candidate.element_stride
                && match &cert.base {
                    Some(crate::facts::ArrayIndexBase::Param { index }) => *index == candidate.slot,
                    Some(crate::facts::ArrayIndexBase::StackSlot { .. }) | None => true,
                }
        })
    }

    fn certified_scalar_array_identity(
        &self,
        prepared: &r2ssa::SsaArtifact,
        memory: &MemoryAccessRenderFact,
        candidate: crate::facts::ScalarArrayRenderCandidate,
    ) -> Option<(r2ssa::SemanticId, r2ssa::SemanticId)> {
        let index = candidate.index_value?;
        let address = prepared.addresses().parameter_expression(memory.address)?;
        let [term] = address.terms.as_slice() else {
            return None;
        };
        if address.parameter != candidate.slot
            || address.offset != i64::try_from(candidate.field_offset).ok()?
            || term.coefficient != i64::try_from(candidate.element_stride).ok()?
            || term.value != index
            || self
                .render
                .parameter_values(candidate.slot)
                .next()
                .is_none()
            || !self
                .render
                .certified_expr_for_value(index)
                .is_some_and(|expr| expr.fact.renderable)
        {
            return None;
        }
        Some((
            r2ssa::SemanticId::parameter(candidate.slot)?,
            r2ssa::SemanticId::expression(index),
        ))
    }

    pub fn type_facts(&self) -> &FunctionTypeFacts {
        &self.types
    }

    #[cfg(test)]
    pub fn __test_type_facts_mut(&mut self) -> &mut FunctionTypeFacts {
        &mut self.types
    }

    #[cfg(test)]
    pub fn __test_render_facts_mut(&mut self) -> &mut FunctionRenderFacts {
        &mut self.render
    }

    pub fn assumptions(&self) -> &r2ssa::AssumptionSet {
        &self.assumptions
    }

    pub fn plans(&self) -> &AnalysisPlans {
        &self.plans
    }

    pub fn summary_view(&self) -> &InterprocSummaryView {
        &self.summary_view
    }

    pub fn diagnostics(&self) -> &[String] {
        &self.diagnostics
    }

    pub fn assumption_usage(&self) -> &r2ssa::AssumptionUsageReport {
        &self.assumption_usage
    }

    pub fn type_plan(&self) -> Option<r2sym::TypePlan> {
        self.plans.type_plan.clone()
    }

    pub fn decompile_plan(&self) -> Option<r2sym::DecompilePlan> {
        self.plans.decompile.clone()
    }

    pub fn query_plan(&self) -> Option<r2sym::QueryPlan> {
        self.plans.query.clone()
    }

    pub fn artifact_build_plan(&self) -> Option<r2sym::ArtifactBuildPlan> {
        self.plans.artifact_build.clone()
    }

    pub fn apply_signature_projection(
        &mut self,
        function_name: &str,
        projection: FunctionSignatureProjection,
        ptr_bits: u32,
    ) -> SignatureProjectionResult {
        self.types
            .apply_signature_projection(function_name, projection, ptr_bits)
    }

    pub fn apply_decompile_type_override(&mut self, override_facts: FunctionTypeFacts) -> bool {
        let Some(signature) = override_facts.render_authorized_signature().cloned() else {
            return false;
        };
        self.types.merged_signature = Some(signature);
        self.types.signature_certificate = override_facts.signature_certificate;
        true
    }

    fn attach_prepared_decompile_evidence(&mut self, prepared: &r2ssa::SsaArtifact) {
        let prepared_callee_resolution = prepared_callee_resolution_facts(prepared, self);
        let prepared_callsites = prepared_callsite_argument_facts(prepared);
        let prepared_call_results = prepared_call_result_facts(prepared);
        let prepared_call_render = prepared_call_render_facts(prepared, &prepared_call_results);
        let prepared_control = prepared_control_facts(prepared);
        let prepared_render = FunctionRenderFacts::from_prepared(prepared);

        // These fields are projections of one exact prepared artifact, not
        // extension points. Letting detached rows win with `or_insert` gave the
        // report and its validator the same stale answer. Advisory type and
        // presentation inputs are consumed while rebuilding, but the resulting
        // source-owned maps are replaced atomically.
        self.callee_resolution = prepared_callee_resolution;
        self.callsites = prepared_callsites;
        self.call_results = prepared_call_results;
        self.call_render = prepared_call_render;
        self.control = prepared_control;
        self.render = prepared_render;
    }

    /// Bind canonical entry values to ABI parameter-slot semantic identities.
    ///
    /// This is a separate step because the ABI profile is owned by the engine,
    /// while expression identity is owned by prepared SSA. Every entry alias is
    /// retained; downstream consumers can select a width without guessing from
    /// register spelling.
    fn populate_certified_parameter_exprs(
        &mut self,
        prepared: &r2ssa::SsaArtifact,
        param_slots: &ParamSlotResolver,
    ) {
        // Register call arguments are implicit machine reads and therefore do
        // not appear in the graph's ordinary use lists. The callsite
        // certificate is their canonical use table; index it once so a formal
        // handed straight to a callee remains a live parameter binding.
        let implicit_call_arguments = prepared
            .certificates()
            .callsites
            .values()
            .flat_map(|callsite| callsite.argument_values.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut entry_values_by_slot = BTreeMap::<u32, (BTreeSet<r2ssa::ValueId>, u32)>::new();
        for value in &prepared.graph().values {
            if value.var.version != 0
                || !parameter_entry_value_has_live_use(prepared, value.id, &implicit_call_arguments)
            {
                continue;
            }
            let Some(slot) = param_slots.slot_for_value(value.id) else {
                continue;
            };
            let Some(parameter_id) = r2ssa::SemanticId::parameter(slot) else {
                continue;
            };
            let Some(cert) = self
                .render
                .certified_exprs
                .get_mut(&r2ssa::SemanticId::expression(value.id))
            else {
                continue;
            };
            cert.bindings.insert(parameter_id);
            let entry = entry_values_by_slot.entry(slot as u32).or_default();
            entry.0.insert(value.id);
            entry.1 = entry.1.max(value.var.size);
        }
        let mut parameter_slot_by_value = entry_values_by_slot
            .iter()
            .flat_map(|(slot, (values, _))| values.iter().map(move |value| (*value, *slot)))
            .collect::<BTreeMap<_, _>>();
        for reload in prepared.certificates().stack_reloads.values() {
            let mut slots = [reload.canonical_source, reload.source]
                .into_iter()
                .filter_map(|value| parameter_slot_by_value.get(&value).copied())
                .collect::<BTreeSet<_>>();
            let Some(slot) = slots.pop_first() else {
                continue;
            };
            if !slots.is_empty() {
                continue;
            }
            let Some(expr) = self
                .render
                .certified_exprs
                .get_mut(&r2ssa::SemanticId::expression(reload.value))
            else {
                continue;
            };
            expr.bindings.insert(r2ssa::SemanticId::Parameter(slot));
            parameter_slot_by_value.insert(reload.value, slot);
        }

        // Preserve exact parameter identity through same-width copies. This is
        // an alias relation, unlike the broader expression dependency walk:
        // arithmetic, loads, casts, and phi nodes never inherit the binding.
        let mut changed = true;
        while changed {
            changed = false;
            for value in &prepared.graph().values {
                if parameter_slot_by_value.contains_key(&value.id) {
                    continue;
                }
                let Some(inst) = prepared
                    .graph()
                    .def_inst(value.id)
                    .and_then(|inst| prepared.graph().inst(inst))
                else {
                    continue;
                };
                let r2ssa::InstPayload::Op(r2ssa::SSAOp::Copy { dst, src }) = &inst.payload else {
                    continue;
                };
                if dst.size != src.size {
                    continue;
                }
                let Some(source) = prepared.graph().value_id_for_var(src) else {
                    continue;
                };
                let Some(slot) = parameter_slot_by_value.get(&source).copied() else {
                    continue;
                };
                let Some(expr) = self
                    .render
                    .certified_exprs
                    .get_mut(&r2ssa::SemanticId::expression(value.id))
                else {
                    continue;
                };
                expr.bindings.insert(r2ssa::SemanticId::Parameter(slot));
                parameter_slot_by_value.insert(value.id, slot);
                changed = true;
            }
        }
        for (slot, (entry_values, carrier_width)) in entry_values_by_slot {
            let id = r2ssa::SemanticId::Parameter(slot);
            let ty = prepared
                .machine_context()
                .function_interface()
                .filter(|interface| {
                    interface
                        .parameters()
                        .get(slot as usize)
                        .is_some_and(|parameter| parameter.index() == slot)
                })
                .and_then(|interface| {
                    let graph = interface.type_graph()?;
                    let logical = interface.parameter_logical_values().get(slot as usize)?;
                    crate::writeback::source_type_like(
                        graph,
                        logical.type_id(),
                        &mut BTreeSet::new(),
                    )
                });
            self.render.certified_entities.insert(
                id,
                CertifiedEntity::Parameter {
                    id,
                    slot,
                    entry_values,
                    carrier_width,
                    ty,
                },
            );
        }
    }

    /// Attach one unambiguous certified type to each loop carrier.
    ///
    /// Carrier identity comes from prepared SSA. Types are projected only from
    /// an exact parameter or return binding already authorized by the function
    /// signature, or from an exact typed memory-access certificate. Conflicting
    /// projections leave the carrier untyped.
    fn populate_certified_loop_carrier_types(&mut self) {
        let signature = self.types.render_authorized_signature().cloned();
        let mut memory_value_types = BTreeMap::<r2ssa::ValueId, CTypeLike>::new();
        let mut conflicting_memory_values = BTreeSet::new();
        for memory in self.render.memory_accesses() {
            let Some(value) = memory.value.filter(|_| !memory.is_write) else {
                continue;
            };
            let Some(ty) = self.render.memory_value_type(memory.access).cloned() else {
                continue;
            };
            match memory_value_types.get(&value) {
                None => {
                    memory_value_types.insert(value, ty);
                }
                Some(existing) if *existing == ty => {}
                Some(_) => {
                    conflicting_memory_values.insert(value);
                }
            }
        }
        for value in conflicting_memory_values {
            memory_value_types.remove(&value);
        }
        let return_values = self
            .render
            .return_effects()
            .map(|fact| fact.value)
            .collect::<BTreeSet<_>>();
        let carriers = self
            .render
            .loop_carriers()
            .filter_map(|entity| match entity {
                CertifiedEntity::LoopCarrier { id, members, .. } => Some((*id, members.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();

        for (id, members) in carriers {
            let mut candidates = Vec::<CTypeLike>::new();
            let carrier_values = members
                .into_iter()
                .map(|member| member.value)
                .collect::<BTreeSet<_>>();
            for value in &carrier_values {
                if let Some(slot) = self.render.exact_parameter_slot_for_value(*value)
                    && let Some(ty) = signature
                        .as_ref()
                        .and_then(|signature| signature.params.get(slot))
                        .and_then(|param| param.ty.clone())
                    && !candidates.contains(&ty)
                {
                    candidates.push(ty);
                }
                if let Some(ty) = memory_value_types.get(value).cloned()
                    && !candidates.contains(&ty)
                {
                    candidates.push(ty);
                }
            }
            if carrier_values
                .iter()
                .any(|value| return_values.contains(value))
                && let Some(ty) = signature
                    .as_ref()
                    .and_then(|signature| signature.ret_type.clone())
                && !candidates.contains(&ty)
            {
                candidates.push(ty);
            }
            let [ty] = candidates.as_slice() else {
                continue;
            };
            if let Some(CertifiedEntity::LoopCarrier {
                ty: carrier_type, ..
            }) = self.render.certified_entities.get_mut(&id)
            {
                *carrier_type = Some(ty.clone());
            }
        }
    }

    /// Project exact callee parameter types back onto caller parameters.
    ///
    /// A constraint is accepted only when the callsite argument has a unique
    /// certified path to one ABI parameter and the callee identity carries a
    /// typed signature. Conflicting callees leave the caller type unchanged.
    pub fn apply_certified_call_argument_type_constraints(&mut self, ptr_bits: u32) -> usize {
        let type_db = &self.types.external_type_db;
        let mut constraints = BTreeMap::<usize, CTypeLike>::new();
        let mut conflicted = BTreeSet::new();
        for (callsite, arguments) in &self.callsites.by_callsite {
            let identity = self.callee_resolution.identity_for_callsite(*callsite);
            let signature = arguments
                .callee_signature
                .as_ref()
                .or_else(|| identity.and_then(crate::CalleeIdentity::known_signature));
            let Some(signature) = signature else {
                continue;
            };
            for argument in &arguments.argument_values {
                let Some(hint) = signature.params.get(argument.index) else {
                    continue;
                };
                let Some(slot) = self
                    .render
                    .unique_parameter_dependency_slot_for_value(argument.value)
                else {
                    continue;
                };
                if conflicted.contains(&slot) {
                    continue;
                }
                match constraints.get(&slot) {
                    None => {
                        constraints.insert(slot, hint.clone());
                    }
                    Some(existing) if existing == hint => {}
                    Some(existing)
                        if crate::signature_hint_can_replace_existing(
                            existing,
                            Some(hint),
                            ptr_bits,
                            type_db,
                        ) =>
                    {
                        constraints.insert(slot, hint.clone());
                    }
                    Some(existing)
                        if crate::signature_hint_can_replace_existing(
                            hint,
                            Some(existing),
                            ptr_bits,
                            type_db,
                        ) => {}
                    Some(_) => {
                        constraints.remove(&slot);
                        conflicted.insert(slot);
                    }
                }
            }
        }

        let protects_existing = self.types.writeback_authorized_signature().is_some();
        let Some(signature) = self.types.merged_signature.as_mut() else {
            return 0;
        };
        let mut applied = BTreeMap::new();
        for (slot, hint) in constraints {
            let Some(param) = signature.params.get_mut(slot) else {
                continue;
            };
            let replace = match param.ty.as_ref() {
                None => true,
                Some(existing) if existing == &hint => false,
                Some(existing) => {
                    !protects_existing
                        && crate::signature_hint_can_replace_existing(
                            existing,
                            Some(&hint),
                            ptr_bits,
                            type_db,
                        )
                }
            };
            if replace {
                param.ty = Some(hint.clone());
                applied.insert(slot, hint);
            }
        }
        if applied.is_empty() {
            return 0;
        }
        for (slot, hint) in &applied {
            if let Some(param) = self.types.register_params.get_mut(*slot) {
                param.ty = Some(hint.clone());
            }
            for binding in self
                .types
                .visible_bindings
                .iter_mut()
                .filter(|binding| binding.param_index == Some(*slot))
            {
                binding.ty = Some(hint.clone());
            }
        }
        self.types
            .certify_current_signature_with_source(SignatureCertificateSource::CalleeSignature);
        applied.len()
    }

    /// Preserve the source-declared logical return type only when every native
    /// return has the exact SSA certificate for that declared carrier. The
    /// immutable interface owns the logical type; the return certificates prove
    /// that this function actually returns a value through that carrier.
    fn apply_exact_source_return_type(&mut self, source: &r2ssa::SsaArtifact) -> bool {
        let Some(return_type) = exact_source_return_type(source) else {
            return false;
        };
        let Some(previous_signature) = self.types.merged_signature.clone() else {
            return false;
        };
        let previous_certificate = self.types.signature_certificate.clone();
        if previous_signature.ret_type.as_ref() == Some(&return_type) {
            if let Some(mut sources) = previous_certificate
                .as_ref()
                .filter(|certificate| certificate.signature == previous_signature)
                .map(|certificate| certificate.sources.clone())
            {
                sources.push(SignatureCertificateSource::SourceReturnType);
                sources.sort();
                sources.dedup();
                if let Some(certificate) =
                    crate::SignatureCertificate::from_signature(&previous_signature, sources)
                {
                    self.types.signature_certificate = Some(certificate);
                }
            }
            return false;
        }
        let Some(signature) = self.types.merged_signature.as_mut() else {
            return false;
        };
        signature.ret_type = Some(return_type);
        let updated_signature = signature.clone();
        let mut sources = previous_certificate
            .as_ref()
            .filter(|certificate| certificate.signature == previous_signature)
            .map(|certificate| certificate.sources.clone())
            .unwrap_or_default();
        // This evidence proves only the return type. Treating it as general
        // ExternalContext evidence would also certify unrelated parameter
        // types and could incorrectly authorize full-signature writeback.
        sources.push(SignatureCertificateSource::SourceReturnType);
        sources.sort();
        sources.dedup();
        let Some(certificate) =
            crate::SignatureCertificate::from_signature(&updated_signature, sources)
        else {
            self.types.merged_signature = Some(previous_signature);
            self.types.signature_certificate = previous_certificate;
            return false;
        };
        self.types.signature_certificate = Some(certificate);
        true
    }

    /// The prototype each call site reaches, keyed the way the solver needs it.
    fn callsite_signatures(&self) -> BTreeMap<r2ssa::CallSiteId, crate::FunctionType> {
        let mut signatures = BTreeMap::new();
        for (callsite, arguments) in &self.callsites.by_callsite {
            let Some(signature) = arguments.callee_signature.as_ref().or_else(|| {
                self.callee_resolution
                    .identity_for_callsite(*callsite)
                    .and_then(crate::CalleeIdentity::known_signature)
            }) else {
                continue;
            };
            signatures.insert(arguments.call_site_id, signature.clone());
        }
        signatures
    }

    /// Type what the code proves, for a function that carries no declared types.
    ///
    /// The solver is given every callee prototype, every certified access width
    /// and every SSA identity at once and run to a fixpoint; what comes back is
    /// only written where the fact it would replace is storage width rather than
    /// evidence, so a recovered type never overwrites a declared one and a value
    /// the solver did not reach keeps whatever it had.
    pub fn apply_recovered_evidence_types(&mut self, source: &r2ssa::SsaArtifact, ptr_bits: u32) {
        let signatures = self.callsite_signatures();
        let recovered = crate::evidence::solve_evidence_types(source, &signatures, ptr_bits);
        if recovered.is_empty() {
            return;
        }
        self.apply_recovered_parameter_types(source, &recovered, ptr_bits);
        self.apply_recovered_return_type(source, &recovered, ptr_bits);
        self.apply_recovered_stack_slot_types(&recovered, ptr_bits);
    }

    /// The type of each exact source parameter value the solver reached.
    ///
    /// Boundary facts own the slot-to-`ValueId` mapping. A missing or
    /// contradictory solution leaves just that parameter unchanged, while a
    /// pointer or operation-proven scalar signedness may replace the weak
    /// machine-width declaration inferred for the same slot.
    fn apply_recovered_parameter_types(
        &mut self,
        source: &r2ssa::SsaArtifact,
        recovered: &crate::EvidenceTypes,
        ptr_bits: u32,
    ) {
        let type_db = &self.types.external_type_db;
        let Some(signature) = self.types.merged_signature.as_mut() else {
            return;
        };
        let mut changed = false;
        for (slot, parameter) in &source.facts().boundaries.parameters {
            if parameter.index != *slot {
                continue;
            }
            let Ok(index) = usize::try_from(*slot) else {
                continue;
            };
            let Some(candidate) = recovered.value_type(parameter.value) else {
                continue;
            };
            let Some(param) = signature.params.get_mut(index) else {
                continue;
            };
            let replace = match param.ty.as_ref() {
                None => true,
                Some(existing) => {
                    recovered_type_outranks(existing, candidate, ptr_bits, type_db)
                        || recovered_scalar_signedness_outranks(existing, candidate, ptr_bits)
                }
            };
            if replace {
                param.ty = Some(candidate.clone());
                changed = true;
            }
        }
        if changed {
            self.types
                .certify_current_signature_with_source(SignatureCertificateSource::LocalInference);
        }
    }

    /// The type of the value the function hands back.
    ///
    /// Only a return that is already claimed to carry a value is retyped: a
    /// function proven to return nothing keeps returning nothing, whatever a
    /// leftover register happens to hold.
    fn apply_recovered_return_type(
        &mut self,
        source: &r2ssa::SsaArtifact,
        recovered: &crate::EvidenceTypes,
        ptr_bits: u32,
    ) {
        let type_db = &self.types.external_type_db;
        let Some(signature) = self.types.merged_signature.as_ref() else {
            return;
        };
        let Some(existing) = signature.ret_type.clone() else {
            return;
        };
        if !crate::facts::is_weak_storage_scalar_type(&existing, ptr_bits) {
            return;
        }

        let mut candidate: Option<CTypeLike> = None;
        for certificate in &source.certificates().returns {
            let Some(ty) = recovered.value_type(certificate.value) else {
                return;
            };
            match &candidate {
                None => candidate = Some(ty.clone()),
                Some(existing) if existing == ty => {}
                // Two returns that disagree have not agreed on a type.
                Some(_) => return,
            }
        }
        let Some(candidate) = candidate else {
            return;
        };
        if !recovered_type_outranks(&existing, &candidate, ptr_bits, type_db) {
            return;
        }
        if let Some(signature) = self.types.merged_signature.as_mut() {
            signature.ret_type = Some(candidate);
        }
        self.types
            .certify_current_signature_with_source(SignatureCertificateSource::CalleeSignature);
    }

    /// The type of each stack home the solver reached.
    fn apply_recovered_stack_slot_types(
        &mut self,
        recovered: &crate::EvidenceTypes,
        ptr_bits: u32,
    ) {
        let type_db = &self.types.external_type_db;
        let mut retyped: Vec<(String, CTypeLike)> = Vec::new();
        for (key, ty) in recovered.stack_slot_types() {
            let Some(slot) = self.types.stack_slots.get_mut(key) else {
                continue;
            };
            let replace = match slot.ty.as_ref() {
                None => true,
                Some(existing) => {
                    recovered_type_outranks(existing, ty, ptr_bits, type_db)
                        || recovered_scalar_signedness_outranks(existing, ty, ptr_bits)
                }
            };
            if !replace {
                continue;
            }
            slot.ty = Some(ty.clone());
            retyped.push((slot.name.clone(), ty.clone()));
        }
        if retyped.is_empty() {
            return;
        }
        for (name, ty) in retyped {
            for binding in self
                .types
                .visible_bindings
                .iter_mut()
                .filter(|binding| binding.name == name)
            {
                let replace = match binding.ty.as_ref() {
                    None => true,
                    Some(existing) => {
                        recovered_type_outranks(existing, &ty, ptr_bits, type_db)
                            || recovered_scalar_signedness_outranks(existing, &ty, ptr_bits)
                    }
                };
                if replace {
                    binding.ty = Some(ty.clone());
                }
            }
        }
    }

    pub fn interproc_summary_set(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.interproc_summary
            .as_ref()
            .map(r2ssa::PreparedInterprocSummarySet::report)
    }

    /// Borrow the advisory report used by pure projection and rendering.
    ///
    /// Unlike [`Self::prepared_interproc_summary`], this report does not prove
    /// ownership of the prepared SSA source and must not authorize mutation or
    /// certification.
    pub fn interproc_summary_report(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.interproc_summary
            .as_ref()
            .map(r2ssa::PreparedInterprocSummarySet::report)
            .or_else(|| self.summary_view.as_set())
    }

    pub fn prepared_interproc_summary(&self) -> Option<&r2ssa::PreparedInterprocSummarySet> {
        self.interproc_summary.as_ref()
    }

    pub fn semantic_artifact(&self) -> Option<&r2sym::SemanticArtifact> {
        self.semantics.as_ref()
    }

    pub fn semantic_report(&self) -> Option<&r2sym::SemanticArtifactReport> {
        self.semantics.as_ref().map(r2sym::SemanticArtifact::report)
    }

    pub fn summary_rollup(&self) -> Option<&SummaryEffectRollup> {
        self.summary_view.rollup.as_ref()
    }

    #[cfg(test)]
    pub fn __test_set_summary_rollup(&mut self, rollup: SummaryEffectRollup) {
        self.summary_view.rollup = Some(rollup);
    }

    pub fn has_assumption_conflicts(&self) -> bool {
        !self.assumption_usage.conflicts.is_empty()
    }

    pub fn has_applied_assumptions(&self) -> bool {
        !self.assumption_usage.applied.is_empty()
    }

    pub fn has_summary_conflicts(&self) -> bool {
        self.summary_view
            .diagnostics()
            .is_some_and(|diagnostics| !diagnostics.converged)
    }

    pub fn decompile_capability(&self) -> DecompileCapabilityView {
        let mut capability = DecompileCapabilityView {
            plan: self.decompile_plan(),
            assumption_conflicted: self.has_assumption_conflicts(),
            summary_conflicted: self.has_summary_conflicts(),
            ..DecompileCapabilityView::default()
        };
        let Some(semantics) = self.semantic_artifact() else {
            return capability;
        };
        capability.slice_class = semantics.slice_class();
        capability.skipped_large_cfg = semantics.diagnostics.skipped_large_cfg;
        capability.has_native_regions = semantics
            .native_body()
            .is_some_and(|body| !body.regions.is_empty());
        capability.has_summary_islands = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_summary_islands);
        capability.has_primary_summary_islands = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_primary_summary_islands);
        capability.summary_island_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::summary_island_count)
            .unwrap_or(0);
        capability.primary_summary_island_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::primary_summary_island_count)
            .unwrap_or(0);
        capability.generic_memory_summary_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::generic_memory_summary_count)
            .unwrap_or(0);
        capability.has_memory_read_write_summary_pair = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_memory_read_write_summary_pair);
        capability.actionable_region_count = semantics.actionable_regions().len();
        capability.ambiguous_targets = semantics.ambiguous_targets();
        capability.residual_reasons = semantics.diagnostics.residual_reasons.clone();
        capability
    }
}

fn parameter_entry_value_has_live_use(
    prepared: &r2ssa::SsaArtifact,
    root: r2ssa::ValueId,
    implicit_call_arguments: &BTreeSet<r2ssa::ValueId>,
) -> bool {
    let graph = prepared.graph();
    let mut pending = vec![root];
    let mut visited = BTreeSet::new();
    while let Some(value) = pending.pop() {
        if !visited.insert(value) {
            continue;
        }
        if implicit_call_arguments.contains(&value) {
            return true;
        }
        for use_site in graph.use_sites(value) {
            let Some(inst) = graph.inst(use_site.inst) else {
                continue;
            };
            if matches!(inst.payload, r2ssa::InstPayload::Phi { .. }) {
                if let Some(output) = inst.output {
                    pending.push(output);
                }
                continue;
            }
            return true;
        }
    }
    false
}

/// Whether a recovered type is better evidence than what is already recorded.
///
/// A width is not a type. A slot that nothing is known about is given the width
/// of the register that spilled it, and any structured type outranks that; a
/// type that is already structured is never demoted, so a recovered type cannot
/// overwrite a declared one.
fn recovered_type_outranks(
    existing: &CTypeLike,
    recovered: &CTypeLike,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    if crate::signature_infer::signature_types_are_equivalent(existing, recovered, ptr_bits) {
        return false;
    }
    if crate::facts::signature_hint_can_replace_existing(
        existing,
        Some(recovered),
        ptr_bits,
        type_db,
    ) {
        return true;
    }
    crate::facts::is_weak_storage_scalar_type(existing, ptr_bits)
        && recovered_type_is_evidence(recovered, ptr_bits)
}

/// Whether a type says more than the width of the storage that held it.
fn recovered_type_is_evidence(ty: &CTypeLike, ptr_bits: u32) -> bool {
    match ty {
        CTypeLike::Pointer(inner) => !matches!(inner.as_ref(), CTypeLike::Unknown),
        CTypeLike::Float(_)
        | CTypeLike::Bool
        | CTypeLike::Struct(_)
        | CTypeLike::Union(_)
        | CTypeLike::Enum(_) => true,
        CTypeLike::Typedef(name) => !crate::facts::is_weak_storage_scalar_typedef(name, ptr_bits),
        _ => false,
    }
}

/// Operation-proven signedness refines a weak scalar of the same width.
fn recovered_scalar_signedness_outranks(
    existing: &CTypeLike,
    recovered: &CTypeLike,
    ptr_bits: u32,
) -> bool {
    let scalar = |ty: &CTypeLike| match ty {
        CTypeLike::Int { bits, signedness } => Some((*bits, *signedness)),
        CTypeLike::Typedef(name) => match crate::parse_c_type_like(name, ptr_bits) {
            Some(CTypeLike::Int { bits, signedness }) => Some((bits, signedness)),
            _ => None,
        },
        _ => None,
    };
    let (Some((existing_bits, existing_signedness)), Some((recovered_bits, recovered_signedness))) =
        (scalar(existing), scalar(recovered))
    else {
        return false;
    };
    existing_bits == recovered_bits
        && existing_signedness != recovered_signedness
        && recovered_signedness != crate::Signedness::Unknown
}

fn struct_name_from_pointer_type(ty: Option<&CTypeLike>) -> Option<&str> {
    let CTypeLike::Pointer(inner) = ty? else {
        return None;
    };
    match inner.as_ref() {
        CTypeLike::Struct(name) | CTypeLike::Typedef(name) => Some(name),
        _ => None,
    }
}

fn prepared_callee_resolution_facts(
    prepared: &r2ssa::SsaArtifact,
    function_facts: &FunctionFacts,
) -> CalleeResolutionFacts {
    let type_facts = function_facts.types.clone().canonicalized();
    // These were empty maps, so every direct call resolved to nothing and
    // rendered as `sub_<addr>` even when radare2 had the name all along.
    let function_names = function_facts
        .display_names
        .functions()
        .iter()
        .map(|(addr, name)| (*addr, name.clone()))
        .collect::<HashMap<_, _>>();
    let symbols = function_facts
        .display_names
        .symbols()
        .iter()
        .map(|(addr, name)| (*addr, name.clone()))
        .collect::<HashMap<_, _>>();
    let known_function_signatures = type_facts
        .known_function_signatures
        .iter()
        .map(|(name, ty)| (crate::normalize_callee_name(name), ty.clone()))
        .collect::<HashMap<_, _>>();
    let ctx = CalleeIdentityContext {
        function_names: &function_names,
        symbols: &symbols,
        callee_facts: &type_facts.callee_facts,
        known_function_signatures: &known_function_signatures,
    };

    CalleeResolutionFacts::from_direct_call_targets(
        prepared
            .call_sites()
            .by_id
            .values()
            .filter_map(|call_site| {
                let direct_target = prepared.resolved_call_target(call_site)?;
                let (block_addr, op_index) = prepared.inst_op_site(call_site.at)?;
                Some((
                    CallsiteKey {
                        block_addr,
                        op_index,
                    },
                    direct_target,
                ))
            }),
        &ctx,
    )
}

fn prepared_callsite_argument_facts(prepared: &r2ssa::SsaArtifact) -> FunctionCallsiteFacts {
    let by_callsite = prepared
        .certificates()
        .callsites
        .values()
        .filter_map(|cert| {
            let (block_addr, op_index) = prepared.inst_op_site(cert.at)?;
            let callsite = CallsiteKey {
                block_addr,
                op_index,
            };
            let argument_values = cert
                .argument_values
                .iter()
                .copied()
                .enumerate()
                .map(|(index, value)| CallArgumentValueFact { index, value })
                .collect();
            let register_argument_locations = cert
                .argument_certificates
                .iter()
                .filter_map(|argument| {
                    let r2ssa::CallArgumentLocation::Register { storage } = &argument.location
                    else {
                        return None;
                    };
                    Some(RegisterCallArgumentLocationFact {
                        index: argument.index,
                        value: argument.value,
                        storage: *storage,
                        source_inst: argument.source_inst,
                    })
                })
                .collect();
            let stack_argument_locations = cert
                .argument_certificates
                .iter()
                .filter_map(|argument| {
                    let r2ssa::CallArgumentLocation::Stack {
                        object,
                        offset,
                        memory_access,
                    } = argument.location
                    else {
                        return None;
                    };
                    Some(StackCallArgumentLocationFact {
                        index: argument.index,
                        value: argument.value,
                        object,
                        offset,
                        memory_access,
                        source_inst: argument.source_inst,
                    })
                })
                .collect();
            Some((
                callsite,
                CallsiteArgumentFacts {
                    callsite,
                    call_site_id: cert.call_site,
                    at: cert.at,
                    target: cert.target,
                    direct_target: cert.direct_target,
                    argument_values,
                    variadic: cert.variadic,
                    fixed_argument_count: cert.fixed_argument_count,
                    // Carrier widths alone do not prove C signedness. A
                    // source-owned callee analysis fills this only after its
                    // exact retained interface matches this call site.
                    callee_signature: None,
                    variadic_argument_count_evidence: cert.variadic_argument_count_evidence,
                    variadic_argument_count_refusal: cert.variadic_argument_count_refusal,
                    register_argument_locations,
                    stack_argument_locations,
                },
            ))
        })
        .collect();
    FunctionCallsiteFacts { by_callsite }
}

fn prepared_call_result_facts(prepared: &r2ssa::SsaArtifact) -> FunctionCallResultFacts {
    let mut by_value = BTreeMap::new();
    let mut by_callsite = BTreeMap::<CallsiteKey, Vec<r2ssa::ValueId>>::new();
    for cert in prepared.certificates().call_results.values() {
        let Some(callsite_cert) = prepared.certificates().callsites.get(&cert.call_site) else {
            continue;
        };
        let callsite = CallsiteKey {
            block_addr: callsite_cert.block_addr,
            op_index: callsite_cert.op_index,
        };
        by_callsite.entry(callsite).or_default().push(cert.value);
        by_value.insert(
            cert.value,
            CallResultFact {
                callsite,
                call_site_id: cert.call_site,
                at: cert.at,
                value: cert.value,
                width: cert.width,
                relation: cert.relation,
                carrier: cert.carrier.clone(),
                owner: cert.owner.clone(),
            },
        );
    }
    FunctionCallResultFacts {
        by_value,
        by_callsite,
    }
}

fn prepared_call_render_facts(
    prepared: &r2ssa::SsaArtifact,
    call_results: &FunctionCallResultFacts,
) -> FunctionCallRenderFacts {
    let by_callsite = prepared
        .certificates()
        .callsites
        .values()
        .map(|cert| {
            let callsite = CallsiteKey {
                block_addr: cert.block_addr,
                op_index: cert.op_index,
            };
            // Whether the call site assigns its result is one question, and
            // `owner_for_site` answers it. Asking a second, narrower one here
            // -- does some result have a *stack slot* owner -- made the two
            // disagree the moment a register-carried result gained an owner:
            // the disposition said side effect while the owner lookup named a
            // value, so the call rendered as a bare statement *and* as its
            // definition's right-hand side, and one site was evaluated twice.
            let count_refusal = if cert.variadic {
                cert.variadic_argument_count_refusal.or_else(|| {
                    cert.variadic_argument_count_evidence.is_none().then_some(
                        r2ssa::VariadicCallsiteArgumentCountRefusal::MissingFormatParameter,
                    )
                })
            } else {
                None
            };
            let disposition = if count_refusal.is_some() {
                CallsiteRenderDisposition::Residualized
            } else if cert.transfer == r2ssa::CallSiteTransfer::TailCall {
                match prepared
                    .facts()
                    .boundaries
                    .calls
                    .get(&cert.call_site)
                    .filter(|boundary| boundary.complete && boundary.at == cert.at)
                    .and_then(|boundary| boundary.result_kind)
                {
                    Some(r2ssa::SourceCallResult::Register { .. }) => {
                        CallsiteRenderDisposition::TerminalReturn
                    }
                    Some(r2ssa::SourceCallResult::Void) => {
                        CallsiteRenderDisposition::TerminalVoidReturn
                    }
                    None => CallsiteRenderDisposition::Residualized,
                }
            } else if call_results.owner_for_site(callsite).is_some() {
                CallsiteRenderDisposition::AssignedResult
            } else {
                CallsiteRenderDisposition::SideEffectStatement
            };
            (
                callsite,
                CallsiteRenderFact {
                    callsite,
                    target: Some(cert.target),
                    disposition,
                    proof_values: cert.argument_values.clone(),
                    residual_reason: count_refusal
                        .map(|refusal| format!("variadic callsite: {}", refusal.kind())),
                },
            )
        })
        .collect();
    FunctionCallRenderFacts { by_callsite }
}

fn prepared_memory_access_field_offset(
    prepared: &r2ssa::SsaArtifact,
    memory: &MemoryAccessRenderFact,
) -> Option<u64> {
    let offset = prepared_address_base_offset(prepared, memory.address, 0)?;
    u64::try_from(offset).ok()
}

fn prepared_memory_access_param_slot(
    prepared: &r2ssa::SsaArtifact,
    memory: &MemoryAccessRenderFact,
    param_slots: &ParamSlotResolver,
) -> Option<usize> {
    prepared_address_base_param_slot(prepared, memory.address, param_slots, 0)
}

fn prepared_memory_access_ptr_bits(
    prepared: &r2ssa::SsaArtifact,
    memory: &MemoryAccessRenderFact,
) -> u32 {
    prepared
        .graph()
        .value(memory.address)
        .map(|value| value.var.size.saturating_mul(8))
        .filter(|bits| *bits > 0)
        .unwrap_or(64)
}

fn prepared_address_base_offset(
    prepared: &r2ssa::SsaArtifact,
    value: r2ssa::ValueId,
    depth: usize,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }
    let graph = prepared.graph();
    let var = &graph.value(value)?.var;
    if const_var_i64(var).is_some() {
        return None;
    }
    if prepared
        .stack_reload_certificate_for_value(value)
        .and_then(|reload| graph.value(reload.canonical_source))
        .is_some_and(|source| source.var.version == 0 && source.var.is_register())
    {
        return Some(0);
    }
    let Some(def_inst) = graph.def_inst(value) else {
        return Some(0);
    };
    let inst = graph.inst(def_inst)?;
    if matches!(inst.payload, r2ssa::InstPayload::Phi { .. }) {
        let mut resolved = None;
        for input in &inst.inputs {
            let Some(offset) = prepared_address_base_offset(prepared, *input, depth + 1) else {
                continue;
            };
            if resolved.is_some_and(|existing| existing != offset) {
                return None;
            }
            resolved = Some(offset);
        }
        return resolved;
    }
    let r2ssa::InstPayload::Op(op) = &inst.payload else {
        unreachable!("handled phi instruction before op matching");
    };
    match op {
        r2ssa::SSAOp::Copy { src, .. }
        | r2ssa::SSAOp::New { src, .. }
        | r2ssa::SSAOp::Cast { src, .. }
        | r2ssa::SSAOp::Subpiece { src, .. }
        | r2ssa::SSAOp::IntZExt { src, .. }
        | r2ssa::SSAOp::IntSExt { src, .. } => prepared_var_base_offset(prepared, src, depth + 1),
        r2ssa::SSAOp::IntAdd { a, b, .. } => {
            prepared_binary_const_offset(prepared, a, b, depth + 1, 1)
        }
        r2ssa::SSAOp::IntSub { a, b, .. } => {
            prepared_binary_const_offset(prepared, a, b, depth + 1, -1)
        }
        r2ssa::SSAOp::PtrAdd {
            base,
            index,
            element_size,
            ..
        } => {
            let delta = const_var_i64(index)?.checked_mul(i64::from(*element_size))?;
            prepared_var_base_offset(prepared, base, depth + 1)?.checked_add(delta)
        }
        r2ssa::SSAOp::PtrSub {
            base,
            index,
            element_size,
            ..
        } => {
            let delta = const_var_i64(index)?.checked_mul(i64::from(*element_size))?;
            prepared_var_base_offset(prepared, base, depth + 1)?.checked_sub(delta)
        }
        _ => None,
    }
}

fn prepared_var_base_offset(
    prepared: &r2ssa::SsaArtifact,
    var: &r2ssa::SSAVar,
    depth: usize,
) -> Option<i64> {
    let value = prepared.graph().value_id_for_var(var)?;
    prepared_address_base_offset(prepared, value, depth)
}

fn prepared_binary_const_offset(
    prepared: &r2ssa::SsaArtifact,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    depth: usize,
    rhs_sign: i64,
) -> Option<i64> {
    match (const_var_i64(a), const_var_i64(b)) {
        (None, Some(rhs)) => {
            let delta = rhs.checked_mul(rhs_sign)?;
            prepared_var_base_offset(prepared, a, depth)?.checked_add(delta)
        }
        (Some(lhs), None) if rhs_sign == 1 => {
            prepared_var_base_offset(prepared, b, depth)?.checked_add(lhs)
        }
        _ => None,
    }
}

fn prepared_address_base_param_slot(
    prepared: &r2ssa::SsaArtifact,
    value: r2ssa::ValueId,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    if depth > 8 {
        return None;
    }
    let graph = prepared.graph();
    let var = &graph.value(value)?.var;
    if const_var_i64(var).is_some() {
        return None;
    }
    if let Some(source) = prepared
        .stack_reload_certificate_for_value(value)
        .and_then(|reload| graph.value(reload.canonical_source))
        && source.var.version == 0
    {
        return param_slots.slot_for_value(source.id);
    }
    let Some(def_inst) = graph.def_inst(value) else {
        return param_slots.slot_for_value(value);
    };
    let inst = graph.inst(def_inst)?;
    if matches!(inst.payload, r2ssa::InstPayload::Phi { .. }) {
        let mut resolved = None;
        for input in &inst.inputs {
            let Some(slot) =
                prepared_address_base_param_slot(prepared, *input, param_slots, depth + 1)
            else {
                continue;
            };
            if resolved.is_some_and(|existing| existing != slot) {
                return None;
            }
            resolved = Some(slot);
        }
        return resolved;
    }
    let r2ssa::InstPayload::Op(op) = &inst.payload else {
        unreachable!("handled phi instruction before op matching");
    };
    match op {
        r2ssa::SSAOp::Copy { src, .. }
        | r2ssa::SSAOp::New { src, .. }
        | r2ssa::SSAOp::Cast { src, .. }
        | r2ssa::SSAOp::Subpiece { src, .. }
        | r2ssa::SSAOp::IntZExt { src, .. }
        | r2ssa::SSAOp::IntSExt { src, .. } => {
            prepared_var_base_param_slot(prepared, src, param_slots, depth + 1)
        }
        r2ssa::SSAOp::IntAdd { a, b, .. } => {
            prepared_add_param_slot(prepared, a, b, param_slots, depth + 1)
        }
        r2ssa::SSAOp::IntSub { a, b, .. } => {
            prepared_sub_param_slot(prepared, a, b, param_slots, depth + 1)
        }
        r2ssa::SSAOp::PtrAdd { base, .. } | r2ssa::SSAOp::PtrSub { base, .. } => {
            prepared_var_base_param_slot(prepared, base, param_slots, depth + 1)
        }
        _ => None,
    }
}

fn prepared_var_base_param_slot(
    prepared: &r2ssa::SsaArtifact,
    var: &r2ssa::SSAVar,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    let value = prepared.graph().value_id_for_var(var)?;
    prepared_address_base_param_slot(prepared, value, param_slots, depth)
}

fn prepared_add_param_slot(
    prepared: &r2ssa::SsaArtifact,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    match (const_var_i64(a), const_var_i64(b)) {
        (None, Some(_)) => prepared_var_base_param_slot(prepared, a, param_slots, depth),
        (Some(_), None) => prepared_var_base_param_slot(prepared, b, param_slots, depth),
        _ => None,
    }
}

fn prepared_sub_param_slot(
    prepared: &r2ssa::SsaArtifact,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    match (const_var_i64(a), const_var_i64(b)) {
        (None, Some(_)) => prepared_var_base_param_slot(prepared, a, param_slots, depth),
        _ => None,
    }
}

fn const_var_i64(var: &r2ssa::SSAVar) -> Option<i64> {
    let raw = var.constant_bits()?;
    let bits = var.size.saturating_mul(8);
    if bits == 0 || bits >= 64 {
        return Some(raw as i64);
    }
    let sign_bit = 1u64.checked_shl(bits - 1)?;
    let mask = 1u64.checked_shl(bits)?.wrapping_sub(1);
    let truncated = raw & mask;
    if truncated & sign_bit == 0 {
        Some(truncated as i64)
    } else {
        Some((truncated | !mask) as i64)
    }
}

fn prepared_predicate_render_comparison<'a>(
    prepared: &r2ssa::SsaArtifact,
    predicate: &'a r2ssa::PredicateFact,
) -> Option<&'a r2ssa::CompareProvenance> {
    predicate
        .evaluated_comparison
        .as_ref()
        .filter(|comparison| {
            [comparison.lhs, comparison.rhs].into_iter().any(|value| {
                prepared
                    .structured()
                    .loops
                    .values()
                    .flat_map(|loop_fact| &loop_fact.carriers)
                    .flat_map(|carrier| &carrier.updates)
                    .any(|update| {
                        update.predecessor == predicate.block_addr
                            && (update.value == value || update.identity_values.contains(&value))
                    })
            })
        })
        .or(predicate.comparison.as_ref())
}

fn prepared_guarded_phi_render_fact(
    prepared: &r2ssa::SsaArtifact,
    value: r2ssa::ValueId,
) -> Option<GuardedPhiRenderFact> {
    let graph = prepared.graph();
    let inst = graph.inst(graph.def_inst(value)?)?;
    let r2ssa::InstPayload::Phi { predecessors } = &inst.payload else {
        return None;
    };
    if predecessors.len() < 2 || predecessors.len() != inst.inputs.len() {
        return None;
    }
    let merge_block = graph.block(inst.block)?.addr;
    let predicates = prepared.predicates();
    let mut arms = Vec::with_capacity(predecessors.len());
    for (predecessor, source) in predecessors.iter().zip(inst.inputs.iter().copied()) {
        let predecessor = graph.block(*predecessor)?.addr;
        let domain = prepared.control_domains().for_block(predecessor)?;
        if !domain.complete {
            return None;
        }
        let mut truths = BTreeMap::new();
        let mut conflicts = BTreeSet::new();
        for guard in &domain.guards {
            let r2ssa::ControlGuard::Branch { predicate, truth } = guard else {
                continue;
            };
            record_guarded_phi_truth(&mut truths, &mut conflicts, *predicate, *truth);
        }
        for assumption in predicates
            .block_assumptions
            .get(&merge_block)
            .into_iter()
            .flatten()
            .filter(|assumption| assumption.predecessor == predecessor)
        {
            record_guarded_phi_truth(
                &mut truths,
                &mut conflicts,
                assumption.predicate,
                assumption.truth,
            );
        }
        for conflict in conflicts {
            truths.remove(&conflict);
        }
        arms.push((source, truths));
    }

    let mut candidates = arms.first()?.1.keys().copied().collect::<BTreeSet<_>>();
    for (_, truths) in arms.iter().skip(1) {
        candidates.retain(|predicate| truths.contains_key(predicate));
    }
    for predicate in candidates {
        let mut when_true = Vec::new();
        let mut when_false = Vec::new();
        for (source, truths) in &arms {
            let truth = *truths.get(&predicate)?;
            let rendered = prepared_guarded_phi_arm_value(prepared, predicate, truth, *source);
            if truth {
                when_true.push((*source, rendered));
            } else {
                when_false.push((*source, rendered));
            }
        }
        if when_true.is_empty() || when_false.is_empty() {
            continue;
        }
        let true_rendered = when_true[0].1;
        let false_rendered = when_false[0].1;
        if when_true
            .iter()
            .any(|(_, rendered)| *rendered != true_rendered)
            || when_false
                .iter()
                .any(|(_, rendered)| *rendered != false_rendered)
        {
            continue;
        }
        return Some(GuardedPhiRenderFact {
            predicate: r2ssa::SemanticId::predicate(predicate),
            when_true: GuardedPhiArmRenderFact {
                sources: when_true
                    .into_iter()
                    .map(|(source, _)| r2ssa::SemanticId::expression(source))
                    .collect(),
                rendered: r2ssa::SemanticId::expression(true_rendered),
            },
            when_false: GuardedPhiArmRenderFact {
                sources: when_false
                    .into_iter()
                    .map(|(source, _)| r2ssa::SemanticId::expression(source))
                    .collect(),
                rendered: r2ssa::SemanticId::expression(false_rendered),
            },
        });
    }
    None
}

fn record_guarded_phi_truth(
    truths: &mut BTreeMap<r2ssa::PredicateId, bool>,
    conflicts: &mut BTreeSet<r2ssa::PredicateId>,
    predicate: r2ssa::PredicateId,
    truth: bool,
) {
    if truths
        .insert(predicate, truth)
        .is_some_and(|existing| existing != truth)
    {
        conflicts.insert(predicate);
    }
}

fn prepared_guarded_phi_arm_value(
    prepared: &r2ssa::SsaArtifact,
    predicate: r2ssa::PredicateId,
    truth: bool,
    source: r2ssa::ValueId,
) -> r2ssa::ValueId {
    let Some(comparison) = prepared
        .predicates()
        .predicates
        .get(&predicate)
        .and_then(|predicate| predicate.comparison.as_ref())
    else {
        return source;
    };
    if !matches!(
        (comparison.kind, truth),
        (r2ssa::CompareKind::Equal, true) | (r2ssa::CompareKind::NotEqual, false)
    ) {
        return source;
    }
    let replacement = if comparison.lhs == source {
        comparison.rhs
    } else if comparison.rhs == source {
        comparison.lhs
    } else {
        return source;
    };
    if prepared
        .value_var(replacement)
        .is_some_and(r2ssa::SSAVar::is_const)
    {
        replacement
    } else {
        source
    }
}

fn prepared_render_facts(prepared: &r2ssa::SsaArtifact) -> FunctionRenderFacts {
    let certificates = prepared.certificates();
    let mut certified_exprs = certificates
        .expressions
        .iter()
        .map(|(value, cert)| {
            let call_result = certificates.call_results.get(value);
            let mut bindings = BTreeSet::new();
            if let Some(result) = call_result {
                bindings.insert(r2ssa::SemanticId::call(result.call_site));
                if let r2ssa::ReturnCarrier::StackSlot { object, .. } = &result.carrier {
                    bindings.insert(r2ssa::SemanticId::stack_slot(*object));
                }
                if let Some(r2ssa::ValueOwner::StackSlot { object, .. }) = &result.owner {
                    bindings.insert(r2ssa::SemanticId::stack_slot(*object));
                }
            }
            let fact = ExpressionRenderFact {
                value: cert.value,
                defining_inst: cert.defining_inst,
                width: cert.width,
                renderable: cert.renderable || call_result.is_some(),
            };
            (
                r2ssa::SemanticId::expression(*value),
                CertifiedExpr {
                    id: r2ssa::SemanticId::expression(*value),
                    fact,
                    inputs: cert
                        .inputs
                        .iter()
                        .copied()
                        .map(r2ssa::SemanticId::expression)
                        .collect(),
                    bindings,
                    guarded_phi: prepared_guarded_phi_render_fact(prepared, *value),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut certified_memory_effects = certificates
        .memory_accesses
        .iter()
        .map(|(access, cert)| {
            let id = r2ssa::SemanticId::memory_access(*access);
            let control_domain = prepared
                .control_domains()
                .for_block(cert.block_addr)
                .expect("memory certificate block has a control domain")
                .clone();
            (
                id,
                CertifiedEffect::Memory {
                    id,
                    fact: MemoryAccessRenderFact {
                        access: cert.access,
                        block_addr: cert.block_addr,
                        op_index: cert.op_index,
                        space: cert.space,
                        object: cert.object,
                        address: cert.address,
                        value: cert.value,
                        is_write: cert.is_write,
                        width: cert.width,
                        materialize_result: false,
                        control_domain,
                    },
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let memory_effects_by_op = certificates
        .memory_accesses_by_op
        .iter()
        .map(|(op, accesses)| {
            (
                *op,
                accesses
                    .iter()
                    .copied()
                    .map(r2ssa::SemanticId::memory_access)
                    .collect(),
            )
        })
        .collect();
    let certified_return_effects = certificates
        .returns
        .iter()
        .map(|cert| {
            let id = r2ssa::SemanticId::return_value(cert.at);
            let control_domain = prepared
                .control_domains()
                .for_block(cert.block_addr)
                .expect("return certificate block has a control domain")
                .clone();
            (
                id,
                CertifiedEffect::Return {
                    id,
                    at: cert.at,
                    fact: ReturnValueRenderFact {
                        block_addr: cert.block_addr,
                        op_index: cert.op_index,
                        value: cert.value,
                        width: cert.width,
                        overlays: cert.overlays.clone(),
                        control_domain,
                    },
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let return_effects_by_op = certified_return_effects
        .iter()
        .filter_map(|(id, effect)| {
            effect
                .return_fact()
                .map(|fact| ((fact.block_addr, fact.op_index), *id))
        })
        .collect();
    let mut certified_entities = certificates
        .stack_slots
        .iter()
        .map(|(object, cert)| {
            let id = r2ssa::SemanticId::stack_slot(*object);
            (
                id,
                CertifiedEntity::StackSlot {
                    id,
                    object: *object,
                    base: cert.base,
                    offset: cert.offset,
                    size: cert.size,
                    array_layout: cert.array_layout.clone(),
                    source_slot: cert.source_slot,
                    callee_allocation: cert.callee_allocation.clone(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let observable_roots = certificates
        .returns
        .iter()
        .map(|cert| cert.value)
        .chain(
            certificates
                .memory_accesses
                .values()
                .flat_map(|cert| std::iter::once(cert.address).chain(cert.value)),
        )
        .chain(certificates.callsites.values().flat_map(|cert| {
            cert.argument_values
                .iter()
                .copied()
                .chain(cert.stack_argument_values.iter().map(|arg| arg.value))
        }))
        .chain(
            prepared
                .predicates()
                .predicates
                .values()
                .flat_map(|predicate| {
                    let mut roots = Vec::new();
                    if let Some(comparison) =
                        prepared_predicate_render_comparison(prepared, predicate)
                    {
                        roots.extend([comparison.lhs, comparison.rhs]);
                    } else {
                        roots.push(predicate.condition);
                    }
                    roots
                }),
        )
        .chain(
            prepared
                .predicates()
                .switches
                .values()
                .filter_map(|switch| switch.selector),
        )
        .collect::<BTreeSet<_>>();
    let mut observable_values = observable_roots.clone();
    let mut pending = observable_values.iter().copied().collect::<Vec<_>>();
    while let Some(value) = pending.pop() {
        let Some(inst) = prepared
            .graph()
            .def_inst(value)
            .and_then(|inst| prepared.graph().inst(inst))
        else {
            continue;
        };
        for input in &inst.inputs {
            if observable_values.insert(*input) {
                pending.push(*input);
            }
        }
    }
    // Whether a carrier is part of the program is a question about the program,
    // and r2ssa is what answers those. Asking instead whether the phi sits in a
    // backward slice from the roots certified so far made publication depend on
    // what else had been certified, so a carrier whose only consumer was the
    // function's own result vanished whenever the return went uncertified.
    let unobserved = prepared.unobserved_merges();
    let mut carrier_edge_roots = Vec::new();
    let mut carrier_identity_values = BTreeSet::new();
    for carrier in prepared
        .structured()
        .loops
        .values()
        .flat_map(|loop_fact| loop_fact.carriers.iter())
        .filter(|carrier| !unobserved.contains(carrier.phi))
    {
        carrier_identity_values.extend(carrier.identity_values.iter().copied());
        carrier_edge_roots.extend(carrier.entries.iter().map(|entry| entry.value));
        carrier_edge_roots.extend(carrier.updates.iter().map(|update| update.value));
        for value in carrier.members.iter().map(|member| member.value) {
            if let Some(expr) = certified_exprs.get_mut(&r2ssa::SemanticId::expression(value)) {
                expr.bindings.insert(carrier.id);
            }
        }
        certified_entities.insert(
            carrier.id,
            CertifiedEntity::LoopCarrier {
                id: carrier.id,
                loop_id: carrier.loop_id,
                header: carrier.header,
                phi: carrier.phi,
                width: carrier.width,
                identity_values: carrier.identity_values.clone(),
                entries: carrier.entries.clone(),
                updates: carrier.updates.clone(),
                dominating_initializers: carrier.dominating_initializers.clone(),
                members: carrier.members.clone(),
                ty: None,
            },
        );
    }
    let consumer_roots = prepared_render_consumer_occurrences(prepared, carrier_edge_roots);
    for effect in certified_memory_effects.values_mut() {
        let CertifiedEffect::Memory { fact, .. } = effect else {
            continue;
        };
        let Some(value) = fact.value.filter(|_| !fact.is_write) else {
            continue;
        };
        if certificates.stack_slots.contains_key(&fact.object) {
            continue;
        }
        // One settled table per value asked about: what a root sees below it is
        // the same answer whichever root reached it.
        let mut settled = BTreeMap::new();
        let dependency_occurrences = consumer_roots.iter().copied().fold(0_u8, |count, root| {
            if count > 1 {
                return count;
            }
            count.saturating_add(
                expression_dependency_occurrences(
                    prepared.graph(),
                    root,
                    value,
                    &carrier_identity_values,
                    &mut BTreeSet::new(),
                    &mut settled,
                )
                .0,
            )
        });
        fact.materialize_result = dependency_occurrences > 1;
    }
    let mut certified_effects = certified_memory_effects;
    certified_effects.extend(certified_return_effects);
    FunctionRenderFacts {
        certified_exprs,
        certified_entities,
        certified_effects,
        return_effects_by_op,
        memory_effects_by_op,
        string_literals_by_value: BTreeMap::new(),
        member_accesses_by_op: BTreeMap::new(),
        array_accesses_by_op: BTreeMap::new(),
    }
}

fn prepared_render_consumer_occurrences(
    prepared: &r2ssa::SsaArtifact,
    carrier_edge_roots: impl IntoIterator<Item = r2ssa::ValueId>,
) -> Vec<r2ssa::ValueId> {
    let certificates = prepared.certificates();
    let mut roots = certificates
        .returns
        .iter()
        .map(|cert| cert.value)
        .collect::<Vec<_>>();
    for cert in certificates.memory_accesses.values() {
        roots.push(cert.address);
        if cert.is_write {
            roots.extend(cert.value);
        }
    }
    for cert in certificates.callsites.values() {
        roots.extend(cert.argument_values.iter().copied());
        roots.extend(cert.stack_argument_values.iter().map(|arg| arg.value));
    }
    for predicate in prepared.predicates().predicates.values() {
        if let Some(comparison) = prepared_predicate_render_comparison(prepared, predicate) {
            roots.extend([comparison.lhs, comparison.rhs]);
        } else {
            roots.push(predicate.condition);
        }
    }
    roots.extend(
        prepared
            .predicates()
            .switches
            .values()
            .filter_map(|switch| switch.selector),
    );
    roots.extend(carrier_edge_roots);
    roots
}

/// How often `target` occurs in the expression rooted at `current`, saturated at two.
///
/// Rendering inlines an expression, so a value reachable by two distinct
/// dependency paths is printed twice, and the caller only needs to know whether
/// that happens at all.
///
/// Enumerating the paths costs one visit per path, which is exponential wherever
/// a subexpression is shared. The same recurrence evaluated once per value is
/// linear in the edges, because how many times `target` occurs below a value
/// does not depend on how the walk arrived at that value. A value is settled
/// only when nothing below it read a value still being computed, since that
/// answer assumed the unfinished value contributes nothing and is true only on
/// the path that made the assumption.
fn expression_dependency_occurrences(
    graph: &r2ssa::SsaGraph,
    current: r2ssa::ValueId,
    target: r2ssa::ValueId,
    carrier_identities: &BTreeSet<r2ssa::ValueId>,
    visiting: &mut BTreeSet<r2ssa::ValueId>,
    settled: &mut BTreeMap<r2ssa::ValueId, u8>,
) -> (u8, bool) {
    if current == target {
        return (1, false);
    }
    if carrier_identities.contains(&current) {
        return (0, false);
    }
    if let Some(known) = settled.get(&current) {
        return (*known, false);
    }
    if !visiting.insert(current) {
        return (0, true);
    }
    let mut count = 0_u8;
    let mut saw_unfinished = false;
    if let Some(inst) = graph.def_inst(current).and_then(|inst| graph.inst(inst)) {
        for input in &inst.inputs {
            if count > 1 {
                break;
            }
            let (below, unfinished) = expression_dependency_occurrences(
                graph,
                *input,
                target,
                carrier_identities,
                visiting,
                settled,
            );
            count = count.saturating_add(below);
            saw_unfinished |= unfinished;
        }
    }
    visiting.remove(&current);
    let count = count.min(2);
    if !saw_unfinished {
        settled.insert(current, count);
    }
    (count, saw_unfinished)
}

fn prepared_control_facts(prepared: &r2ssa::SsaArtifact) -> FunctionControlFacts {
    let predicates = prepared.predicates();
    let certificates = prepared.certificates();
    let branch_predicates = predicates
        .predicates
        .values()
        .map(|predicate| {
            (
                predicate.block_addr,
                BranchPredicateFact {
                    id: predicate.id,
                    block_addr: predicate.block_addr,
                    condition: predicate.condition,
                    comparison: predicate.comparison.as_ref().map(|comparison| {
                        PredicateComparisonFact {
                            kind: comparison.kind,
                            lhs: comparison.lhs,
                            rhs: comparison.rhs,
                        }
                    }),
                    evaluated_comparison: predicate.evaluated_comparison.as_ref().map(
                        |comparison| PredicateComparisonFact {
                            kind: comparison.kind,
                            lhs: comparison.lhs,
                            rhs: comparison.rhs,
                        },
                    ),
                    render_comparison: prepared_predicate_render_comparison(prepared, predicate)
                        .map(|comparison| PredicateComparisonFact {
                            kind: comparison.kind,
                            lhs: comparison.lhs,
                            rhs: comparison.rhs,
                        }),
                    true_target: predicate.true_target,
                    false_target: predicate.false_target,
                },
            )
        })
        .collect();
    let block_assumptions = predicates
        .block_assumptions
        .iter()
        .map(|(block_addr, assumptions)| {
            (
                *block_addr,
                assumptions
                    .iter()
                    .map(|assumption| ControlBlockAssumptionFact {
                        predecessor: assumption.predecessor,
                        predicate: assumption.predicate,
                        truth: assumption.truth,
                    })
                    .collect(),
            )
        })
        .collect();
    let loops = certificates
        .loops
        .iter()
        .map(|(loop_id, cert)| {
            (
                *loop_id,
                LoopStructureFact {
                    loop_id: *loop_id,
                    proof_node: cert.proof_node.to_string(),
                    header: cert.header,
                    condition: cert.condition,
                    condition_value: cert.condition.and_then(|id| {
                        predicates
                            .predicates
                            .get(&id)
                            .map(|predicate| predicate.condition)
                    }),
                    body: sorted_u64s(&cert.body),
                    latches: sorted_u64s(&cert.latches),
                    exits: sorted_u64s(&cert.exits),
                    for_loop: cert.for_loop.clone(),
                },
            )
        })
        .collect();
    let switches = predicates
        .switches
        .iter()
        .map(|(block_addr, switch)| {
            (
                *block_addr,
                SwitchSelectorFact {
                    proof_node: r2ssa::ProofNodeId::switch_certificate(*block_addr).to_string(),
                    block_addr: switch.block_addr,
                    selector: switch.selector,
                    cases: switch.cases.clone(),
                    default: switch.default,
                },
            )
        })
        .collect();
    FunctionControlFacts {
        branch_predicates,
        block_assumptions,
        loops,
        switches,
        control_domains: prepared.control_domains().clone(),
    }
}

fn sorted_u64s(values: &[u64]) -> Vec<u64> {
    let mut values = values.to_vec();
    values.sort_unstable();
    values
}

fn summary_rollup(set: Option<&r2ssa::InterprocSummarySet>) -> Option<SummaryEffectRollup> {
    let set = set?;
    let root_summary = set.root.and_then(|root| set.summaries.get(&root));
    let out_param_facts = root_summary
        .map(summary_out_param_facts)
        .unwrap_or_default();

    let mut pointer_param_indices = root_summary
        .map(|summary| {
            let mut indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| {
                    (effect.read || effect.write || effect.escape || effect.free).then_some(*idx)
                })
                .collect::<Vec<_>>();
            for effect in &summary.memory_effects {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region {
                    indices.push(index);
                }
            }
            push_structured_summary_pointer_indices(summary, &mut indices);
            indices
        })
        .unwrap_or_default();
    pointer_param_indices.sort_unstable();
    pointer_param_indices.dedup();

    Some(SummaryEffectRollup {
        root_name: root_summary.and_then(|summary| summary.name.clone()),
        root_return_relation: root_summary.map(|summary| summary.return_relation.clone()),
        out_param_facts,
        pointer_param_indices,
        transfer_count: root_summary.map_or(0, |summary| summary.transfer_effects.len()),
        allocation_count: root_summary.map_or(0, |summary| summary.allocation_effects.len()),
        lifetime_count: root_summary.map_or(0, |summary| summary.lifetime_effects.len()),
        sync_count: root_summary.map_or(0, |summary| summary.sync_effects.len()),
        atomic_count: root_summary.map_or(0, |summary| summary.atomic_effects.len()),
        helper_summary_count: set
            .summaries
            .len()
            .saturating_sub(usize::from(set.root.is_some())),
        has_unknown_calls: root_summary.is_some_and(|summary| summary.has_unknown_calls),
        touches_unknown_memory: root_summary.is_some_and(|summary| summary.touches_unknown_memory),
    })
}

fn helper_views(set: Option<&r2ssa::InterprocSummarySet>) -> Vec<SummaryHelperView> {
    let Some(set) = set else {
        return Vec::new();
    };
    let mut helpers = set
        .summaries
        .iter()
        .filter(|(id, _)| Some(**id) != set.root)
        .map(|(id, summary)| {
            let out_param_facts = summary_out_param_facts(summary);

            let mut pointer_param_indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| {
                    (effect.read || effect.write || effect.escape || effect.free).then_some(*idx)
                })
                .collect::<Vec<_>>();
            for effect in &summary.memory_effects {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region {
                    pointer_param_indices.push(index);
                }
            }
            push_structured_summary_pointer_indices(summary, &mut pointer_param_indices);
            pointer_param_indices.sort_unstable();
            pointer_param_indices.dedup();

            SummaryHelperView {
                function_id: id.0,
                name: summary.name.clone(),
                arg_count_hint: summary.arg_count_hint,
                return_relation: summary.return_relation.clone(),
                out_param_facts,
                pointer_param_indices,
                transfer_effects: summary.transfer_effects.clone(),
                allocation_effects: summary.allocation_effects.clone(),
                lifetime_effects: summary.lifetime_effects.clone(),
                sync_effects: summary.sync_effects.clone(),
                atomic_effects: summary.atomic_effects.clone(),
                has_unknown_calls: summary.has_unknown_calls,
                touches_unknown_memory: summary.touches_unknown_memory,
            }
        })
        .collect::<Vec<_>>();
    helpers.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then(left.function_id.cmp(&right.function_id))
    });
    helpers
}

fn summary_out_param_facts(summary: &r2ssa::FunctionSemanticSummary) -> Vec<SummaryOutParamFact> {
    let mut facts = summary
        .arg_effects
        .iter()
        .enumerate()
        .filter(|(_, (_, effect))| effect.write)
        .map(|(effect_index, (idx, _))| SummaryOutParamFact {
            param_index: *idx,
            evidence: OutParamCertificateEvidence::InterprocArgWrite,
            source: OutParamCertificateSource::InterprocSummaryEffect {
                function_id: summary.id.0,
                evidence: OutParamCertificateEvidence::InterprocArgWrite,
                param_index: *idx,
                effect_index,
            },
        })
        .collect::<Vec<_>>();
    for (effect_index, effect) in summary.memory_effects.iter().enumerate() {
        if effect.kind == r2ssa::SummaryMemoryEffectKind::Write
            && let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region
        {
            facts.push(SummaryOutParamFact {
                param_index: index,
                evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                source: OutParamCertificateSource::InterprocSummaryEffect {
                    function_id: summary.id.0,
                    evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                    param_index: index,
                    effect_index,
                },
            });
        }
    }
    for (effect_index, effect) in summary.transfer_effects.iter().enumerate() {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            facts.push(SummaryOutParamFact {
                param_index: index,
                evidence: OutParamCertificateEvidence::InterprocTransferDst,
                source: OutParamCertificateSource::InterprocSummaryEffect {
                    function_id: summary.id.0,
                    evidence: OutParamCertificateEvidence::InterprocTransferDst,
                    param_index: index,
                    effect_index,
                },
            });
        }
    }
    facts.sort();
    facts.dedup();
    facts
}

fn out_param_indices_from_facts(facts: &[SummaryOutParamFact]) -> Vec<usize> {
    let mut indices = facts
        .iter()
        .map(|fact| fact.param_index)
        .collect::<Vec<_>>();
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn push_structured_summary_pointer_indices(
    summary: &r2ssa::FunctionSemanticSummary,
    indices: &mut Vec<usize>,
) {
    for effect in &summary.transfer_effects {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            indices.push(index);
        }
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.src.region {
            indices.push(index);
        }
    }
    for effect in &summary.lifetime_effects {
        indices.push(effect.arg);
    }
    for effect in &summary.sync_effects {
        indices.push(effect.arg);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExternalStackBase, FunctionParamSpec};
    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
        RegisterProjectionDisposition, RegisterStorage, SpaceId, Varnode,
    };
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    #[test]
    fn constant_looking_spelling_is_not_constant_evidence() {
        assert_eq!(
            const_var_i64(&r2ssa::SSAVar::new("const:ffffffffffffffb8", 0, 8)),
            None
        );
        assert_eq!(
            const_var_i64(&r2ssa::SSAVar::constant(0xffff_ffff_ffff_ffb8, 8)),
            Some(-72)
        );
    }

    #[test]
    fn parameter_coalescing_values_are_exact_entry_membership() {
        let entry_values =
            BTreeSet::from([r2ssa::ValueId(7), r2ssa::ValueId(2), r2ssa::ValueId(11)]);
        let entity = CertifiedEntity::Parameter {
            id: r2ssa::SemanticId::Parameter(0),
            slot: 0,
            entry_values: entry_values.clone(),
            carrier_width: 8,
            ty: None,
        };

        assert_eq!(entity.coalescing_values(), Some(entry_values));
    }

    #[test]
    fn loop_carrier_coalescing_values_cover_every_program_point_role() {
        let entity = CertifiedEntity::LoopCarrier {
            id: r2ssa::SemanticId::LoopCarrier(r2ssa::ValueId(1)),
            loop_id: r2ssa::LoopId(0),
            header: 0x401000,
            phi: r2ssa::ValueId(1),
            width: 4,
            identity_values: BTreeSet::from([r2ssa::ValueId(4), r2ssa::ValueId(1)]),
            entries: vec![
                r2ssa::LoopCarrierEdgeValue {
                    predecessor: 0x400ff0,
                    value: r2ssa::ValueId(7),
                    site: r2ssa::UseSite {
                        inst: r2ssa::InstId(20),
                        input_idx: 0,
                    },
                },
                r2ssa::LoopCarrierEdgeValue {
                    predecessor: 0x400fe0,
                    value: r2ssa::ValueId(3),
                    site: r2ssa::UseSite {
                        inst: r2ssa::InstId(20),
                        input_idx: 1,
                    },
                },
            ],
            updates: vec![r2ssa::LoopCarrierUpdateFact {
                predecessor: 0x401010,
                value: r2ssa::ValueId(9),
                site: r2ssa::UseSite {
                    inst: r2ssa::InstId(20),
                    input_idx: 2,
                },
                identity_values: BTreeSet::from([r2ssa::ValueId(8), r2ssa::ValueId(2)]),
            }],
            dominating_initializers: vec![
                r2ssa::LoopCarrierEdgeValue {
                    predecessor: 0x400fd0,
                    value: r2ssa::ValueId(6),
                    site: r2ssa::UseSite {
                        inst: r2ssa::InstId(30),
                        input_idx: 0,
                    },
                },
                r2ssa::LoopCarrierEdgeValue {
                    predecessor: 0x400fc0,
                    value: r2ssa::ValueId(3),
                    site: r2ssa::UseSite {
                        inst: r2ssa::InstId(30),
                        input_idx: 1,
                    },
                },
            ],
            members: [1, 2, 3, 4, 6, 7, 8, 9]
                .into_iter()
                .map(|value| r2ssa::LoopCarrierMemberFact {
                    value: r2ssa::ValueId(value),
                    roles: BTreeSet::from([r2ssa::LoopCarrierMemberRole::StorageContinuation]),
                })
                .collect(),
            ty: None,
        };

        assert_eq!(
            entity.coalescing_values(),
            Some(BTreeSet::from([
                r2ssa::ValueId(1),
                r2ssa::ValueId(2),
                r2ssa::ValueId(3),
                r2ssa::ValueId(4),
                r2ssa::ValueId(6),
                r2ssa::ValueId(7),
                r2ssa::ValueId(8),
                r2ssa::ValueId(9),
            ]))
        );
    }

    #[test]
    fn coalescing_membership_is_order_independent_and_stack_slots_refuse_it() {
        let edge = |predecessor, value| r2ssa::LoopCarrierEdgeValue {
            predecessor,
            value: r2ssa::ValueId(value),
            site: r2ssa::UseSite {
                inst: r2ssa::InstId(value),
                input_idx: 0,
            },
        };
        let update = |predecessor, value, identities| r2ssa::LoopCarrierUpdateFact {
            predecessor,
            value: r2ssa::ValueId(value),
            site: r2ssa::UseSite {
                inst: r2ssa::InstId(value),
                input_idx: 0,
            },
            identity_values: identities,
        };
        let make_carrier =
            |entries, updates, dominating_initializers, members| CertifiedEntity::LoopCarrier {
                id: r2ssa::SemanticId::LoopCarrier(r2ssa::ValueId(1)),
                loop_id: r2ssa::LoopId(0),
                header: 0x401000,
                phi: r2ssa::ValueId(1),
                width: 8,
                identity_values: BTreeSet::from([r2ssa::ValueId(5), r2ssa::ValueId(1)]),
                entries,
                updates,
                dominating_initializers,
                members,
                ty: None,
            };
        let members = |values: Vec<u32>| {
            values
                .into_iter()
                .map(|value| r2ssa::LoopCarrierMemberFact {
                    value: r2ssa::ValueId(value),
                    roles: BTreeSet::from([r2ssa::LoopCarrierMemberRole::StorageContinuation]),
                })
                .collect::<Vec<_>>()
        };
        let forward = make_carrier(
            vec![edge(10, 2), edge(20, 3)],
            vec![
                update(30, 4, BTreeSet::from([r2ssa::ValueId(6)])),
                update(40, 7, BTreeSet::from([r2ssa::ValueId(8)])),
            ],
            vec![edge(50, 9), edge(60, 10)],
            members(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        );
        let reversed = make_carrier(
            vec![edge(20, 3), edge(10, 2)],
            vec![
                update(40, 7, BTreeSet::from([r2ssa::ValueId(8)])),
                update(30, 4, BTreeSet::from([r2ssa::ValueId(6)])),
            ],
            vec![edge(60, 10), edge(50, 9)],
            members(vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1]),
        );
        let object = r2ssa::ObjectId(3);
        let stack_slot = CertifiedEntity::StackSlot {
            id: r2ssa::SemanticId::stack_slot(object),
            object,
            base: r2ssa::StackAddressBase::FramePointer,
            offset: -8,
            size: Some(8),
            array_layout: r2ssa::StackArrayLayoutDisposition::NotIndexed,
            source_slot: None,
            callee_allocation: None,
        };

        assert_eq!(forward.coalescing_values(), reversed.coalescing_values());
        assert_eq!(stack_slot.coalescing_values(), None);
    }

    #[test]
    fn exact_source_param_slots_ignore_misleading_register_names() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rax", 0x20, 8));
        arch.add_register(RegisterDef::new("not_an_argument", 0x20, 4));
        arch.add_register(RegisterDef::new("rdi", 0x30, 8));
        arch.add_register(RegisterDef::new("rip", 0x40, 8));
        let storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0x20,
            size: 8,
        };
        let logical = r2ssa::SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64),
        );
        let type_graph = r2ssa::SourceTypeGraph::new(
            [r2ssa::SourceType::new(
                0,
                r2ssa::SourceTypeKind::UnsignedInteger,
                64,
                64,
            )],
            [],
        )
        .expect("exact parameter type graph");
        let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            b"exact-param-alias".to_vec(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(0, storage)],
            r2ssa::SourceFunctionReturn::Void,
            [],
            [logical],
            None,
            Some(type_graph),
        )
        .and_then(|interface| {
            interface.with_stack_pointer_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x30,
                size: 8,
            })
        })
        .and_then(|interface| {
            interface.with_return_address_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x40,
                size: 8,
            })
        })
        .expect("exact interface");
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::register(0x20, 8),
        });
        let source =
            r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("prepared source");

        let resolver = exact_source_param_slot_resolver(&source).expect("exact resolver");
        let parameter = source
            .facts()
            .boundaries
            .parameters
            .get(&0)
            .expect("exact boundary parameter");
        assert_eq!(resolver.slot_for_value(parameter.value), Some(0));
        let parameter_var = &source
            .graph()
            .value(parameter.value)
            .expect("parameter graph value")
            .var;
        assert_eq!(
            source
                .decompile_prep_facts()
                .and_then(|facts| facts.formal_parameter_of(parameter_var)),
            Some(0),
            "SSA preparation must consume the same exact boundary slot"
        );
        assert_eq!(
            Some(parameter_var.name.as_str()),
            Some("rax"),
            "the deliberately ABI-misleading display name must not change the slot"
        );
    }

    #[test]
    fn exact_source_param_slots_refuse_missing_interface() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rdi", 0x20, 8));
        let source = r2ssa::SsaArtifact::for_decompile(&[R2ILBlock::new(0x1000, 1)], Some(&arch))
            .expect("prepared source without interface");

        assert!(exact_source_param_slot_resolver(&source).is_none());
    }

    fn exact_signed_i32_return_source(has_return: bool) -> r2ssa::SsaArtifact {
        let mut arch = ArchSpec::new("x86-64");
        for (name, offset, size) in [
            ("rax", 0x00, 8),
            ("eax", 0x00, 4),
            ("rsp", 0x28, 8),
            ("rip", 0x30, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        let projection = |written: RegisterStorage, carrier: RegisterStorage, size_bits: u64| {
            RegisterProjection {
                written,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits,
                    },
                },
            }
        };
        arch.register_projections = vec![
            projection(
                RegisterStorage { offset: 0, size: 8 },
                RegisterStorage { offset: 0, size: 8 },
                64,
            ),
            projection(
                RegisterStorage { offset: 0, size: 4 },
                RegisterStorage { offset: 0, size: 8 },
                32,
            ),
            projection(
                RegisterStorage {
                    offset: 0x28,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x28,
                    size: 8,
                },
                64,
            ),
            projection(
                RegisterStorage {
                    offset: 0x30,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x30,
                    size: 8,
                },
                64,
            ),
        ];
        let mut block = R2ILBlock::new(0x401000, 2);
        // An arithmetic write followed by the carrier clear the lift states
        // for it. Arithmetic rather than a copy so the narrow result survives
        // as its own definition instead of being folded into its uses, and the
        // extension has an `eax` to name.
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 4),
            a: Varnode::register(0, 4),
            b: Varnode::constant(7, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: Varnode::register(0, 8),
            src: Varnode::register(0, 4),
        });
        if has_return {
            block.push(R2ILOp::Return {
                target: Varnode::register(0x30, 8),
            });
        }
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let logical = r2ssa::SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32),
        );
        let graph = r2ssa::SourceTypeGraph::new(
            [r2ssa::SourceType::new(
                0,
                r2ssa::SourceTypeKind::SignedInteger,
                32,
                32,
            )],
            [],
        )
        .expect("exact signed return graph");
        let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            b"exact-signed-return".to_vec(),
            "sysv64",
            [],
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            [],
            Some(logical),
            Some(graph),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .expect("exact signed return interface");
        r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("prepared signed return source")
    }

    #[test]
    fn exact_source_return_type_preserves_signed_i32_with_matching_certificate() {
        let source = exact_signed_i32_return_source(true);

        assert_eq!(
            exact_source_return_type(&source),
            Some(CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            })
        );

        let signature = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            }),
            params: Vec::new(),
        };
        let mut facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature.clone()),
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &signature,
                    [crate::SignatureCertificateSource::ExternalContext],
                ),
                ..FunctionTypeFacts::default()
            },
            None,
        );
        assert!(!facts.apply_exact_source_return_type(&source));
        assert!(
            facts
                .type_facts()
                .signature_certificate
                .as_ref()
                .is_some_and(|certificate| certificate
                    .sources
                    .contains(&crate::SignatureCertificateSource::SourceReturnType))
        );
    }

    #[test]
    fn exact_source_return_type_refuses_missing_or_mismatched_certificate() {
        let missing = exact_signed_i32_return_source(false);
        assert!(missing.certificates().returns.is_empty());
        assert_eq!(exact_source_return_type(&missing), None);

        let matching = exact_signed_i32_return_source(true);
        let mut mismatched = matching.certificates().returns[0].clone();
        mismatched.width = 8;
        let logical = matching
            .machine_context()
            .function_interface()
            .and_then(r2ssa::SourceFunctionInterface::return_logical_value)
            .expect("exact logical return");
        assert!(!exact_return_certificate_matches(
            &mismatched,
            logical,
            4,
            &r2ssa::ReturnCarrier::Register {
                storage: r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
            },
        ));
        let mut forged_logical = matching.certificates().returns[0].clone();
        forged_logical.source_logical_value = None;
        assert!(!exact_return_certificate_matches(
            &forged_logical,
            logical,
            4,
            &r2ssa::ReturnCarrier::Register {
                storage: r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
            },
        ));
    }

    #[test]
    fn exact_tail_return_requires_a_complete_matching_source_boundary() {
        let storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let target_storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Ram,
            offset: 0x402000,
            size: 8,
        };
        let call_site_id = r2ssa::CallSiteId(0);
        let at = r2ssa::InstId(3);
        let target = r2ssa::ValueId(7);
        let call_site = r2ssa::CallSiteFact {
            id: call_site_id,
            at,
            raw_identity: Some(r2ssa::SourceCallSiteIdentity::new(
                0x401000,
                2,
                target_storage,
            )),
            target,
            direct_target: Some(0x402000),
            fallthrough: None,
            transfer: r2ssa::CallSiteTransfer::TailCall,
            memory_effect: r2ssa::CallMemoryEffect::Unknown,
        };
        let certificate = r2ssa::CallsiteCertificate {
            call_site: call_site_id,
            at,
            block_addr: 0x401000,
            op_index: 2,
            target,
            direct_target: Some(0x402000),
            fallthrough: None,
            transfer: r2ssa::CallSiteTransfer::TailCall,
            argument_values: Vec::new(),
            variadic: false,
            fixed_argument_count: Some(0),
            variadic_argument_count_evidence: None,
            variadic_argument_count_refusal: None,
            stack_argument_values: Vec::new(),
            argument_certificates: Vec::new(),
        };
        let mut boundary = r2ssa::SourceCallBoundaryFact {
            call_site: call_site_id,
            at,
            calling_convention: Some("sysv64".to_string()),
            variadic: Some(false),
            noreturn: Some(false),
            result_kind: Some(r2ssa::SourceCallResult::Register { storage }),
            arguments: Vec::new(),
            fixed_argument_count: Some(0),
            variadic_argument_count_evidence: None,
            variadic_argument_count_refusal: None,
            results: Vec::new(),
            complete: true,
        };

        assert!(exact_tail_return_certificate_matches(
            &call_site,
            &certificate,
            &boundary,
            storage,
        ));

        boundary.complete = false;
        assert!(!exact_tail_return_certificate_matches(
            &call_site,
            &certificate,
            &boundary,
            storage,
        ));
        boundary.complete = true;
        boundary.result_kind = Some(r2ssa::SourceCallResult::Void);
        assert!(!exact_tail_return_certificate_matches(
            &call_site,
            &certificate,
            &boundary,
            storage,
        ));
    }

    #[test]
    fn exact_source_param_slots_accept_exact_empty_interface() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rsp", 0x30, 8));
        arch.add_register(RegisterDef::new("rip", 0x40, 8));
        let register_storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"exact-empty-interface".to_vec(),
            "sysv64",
            [],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0x30)))
        .and_then(|interface| interface.with_return_address_storage(register_storage(0x40)))
        .expect("exact empty interface");
        let source = r2ssa::SsaArtifact::for_decompile_with_interface(
            &[R2ILBlock::new(0x1000, 1)],
            Some(&arch),
            interface,
        )
        .expect("prepared source");

        assert!(
            exact_source_param_slot_resolver(&source)
                .expect("empty resolver")
                .is_empty()
        );
    }

    fn test_control_domain() -> r2ssa::ControlDomain {
        r2ssa::ControlDomain {
            id: r2ssa::ControlDomainId(0),
            guards: Vec::new(),
            loops: Vec::new(),
            complete: true,
        }
    }

    fn test_render_with_stack_slots<const N: usize>(
        slots: [(r2ssa::ObjectId, r2ssa::StackAddressBase, i64); N],
    ) -> FunctionRenderFacts {
        FunctionRenderFacts {
            certified_entities: slots
                .into_iter()
                .map(|(object, base, offset)| {
                    let id = r2ssa::SemanticId::stack_slot(object);
                    (
                        id,
                        CertifiedEntity::StackSlot {
                            id,
                            object,
                            base,
                            offset,
                            size: None,
                            array_layout: r2ssa::StackArrayLayoutDisposition::NotIndexed,
                            source_slot: None,
                            callee_allocation: None,
                        },
                    )
                })
                .collect(),
            ..FunctionRenderFacts::default()
        }
    }

    #[test]
    fn function_facts_owns_input_quality_evidence() {
        let complete = FunctionInputQualityFacts {
            expected_blocks: 2,
            lifted_blocks: 2,
            actual_lifted_blocks: 2,
            read_failures: 0,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: None,
        };
        assert!(complete.is_complete());

        let refused = FunctionInputQualityFacts {
            expected_blocks: 2,
            lifted_blocks: 1,
            actual_lifted_blocks: 1,
            read_failures: 1,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: Some("incomplete lifted function input".to_string()),
        };
        assert!(!refused.is_complete());

        let mismatch = FunctionInputQualityFacts {
            expected_blocks: 2,
            lifted_blocks: 2,
            actual_lifted_blocks: 1,
            read_failures: 0,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: Some("inconsistent lifted function input".to_string()),
        };
        assert!(!mismatch.is_complete());

        let mut facts = FunctionFacts::default().with_input_quality(refused.clone());
        assert_eq!(facts.input_quality(), Some(&refused));
        assert!(
            !facts.input_quality().expect("quality fact").is_complete(),
            "incomplete lift quality must travel as refusal evidence"
        );

        facts.set_input_quality(Some(complete.clone()));
        assert_eq!(facts.input_quality(), Some(&complete));
        assert!(facts.input_quality().expect("quality fact").is_complete());

        facts.set_input_quality(Some(mismatch.clone()));
        assert_eq!(facts.input_quality(), Some(&mismatch));
        assert!(!facts.input_quality().expect("quality fact").is_complete());

        facts.set_input_quality(None);
        assert_eq!(facts.input_quality(), None);
    }

    #[test]
    fn function_facts_owns_canonical_callee_resolution() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 3,
        };
        let function_names = HashMap::from([(0x402000, "sym.helper".to_string())]);
        let symbols = HashMap::new();
        let known_function_signatures = HashMap::new();
        let callee_facts = BTreeMap::new();
        let ctx = crate::CalleeIdentityContext {
            function_names: &function_names,
            symbols: &symbols,
            callee_facts: &callee_facts,
            known_function_signatures: &known_function_signatures,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x402000)], &ctx);

        let facts = FunctionFacts::default().with_callee_resolution(resolution);

        assert!(
            facts
                .callee_resolution()
                .and_then(|resolution| resolution.identity_for_callsite(callsite))
                .is_some(),
            "callsite identity must travel through FunctionFacts, not a render side channel"
        );
    }

    #[test]
    fn prepared_display_name_does_not_create_a_known_signature() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x402000, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared direct call");
        let callsite = CallsiteKey {
            block_addr: 0x401000,
            op_index: 0,
        };
        let mut names = crate::DisplayNames::default();
        names.insert_function(0x402000, "sym.imp.__memcpy_chk");
        let mut facts = FunctionFacts::default();
        facts.set_display_names(names);

        facts.attach_prepared_decompile_evidence(&prepared);

        let identity = facts
            .callee_resolution()
            .and_then(|resolution| resolution.identity_for_callsite(callsite))
            .expect("direct target identity");
        assert_eq!(identity.raw_name(), "sym.imp.__memcpy_chk");
        assert!(identity.known_signature().is_none());
        assert_eq!(identity.non_variadic_known_arity(), None);
    }

    #[test]
    fn function_facts_owns_canonical_callsite_arguments() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let value = r2ssa::ValueId(11);
        let callsites = FunctionCallsiteFacts {
            by_callsite: BTreeMap::from([(
                callsite,
                CallsiteArgumentFacts {
                    callsite,
                    call_site_id: r2ssa::CallSiteId(2),
                    at: r2ssa::InstId(5),
                    target: r2ssa::ValueId(10),
                    direct_target: Some(0x402000),
                    argument_values: vec![CallArgumentValueFact { index: 0, value }],
                    variadic: false,
                    fixed_argument_count: None,
                    callee_signature: None,
                    variadic_argument_count_evidence: None,
                    variadic_argument_count_refusal: None,
                    register_argument_locations: vec![RegisterCallArgumentLocationFact {
                        index: 0,
                        value,
                        storage: r2ssa::CanonicalStorageId {
                            space: r2ssa::CanonicalStorageSpace::Register,
                            offset: 0,
                            size: 8,
                        },
                        source_inst: Some(r2ssa::InstId(4)),
                    }],
                    stack_argument_locations: Vec::new(),
                },
            )]),
        };

        let facts = FunctionFacts::default().with_callsites(callsites);

        assert_eq!(
            facts
                .callsites()
                .and_then(|callsites| callsites.arguments_for_site(callsite))
                .and_then(|args| args.argument_value(0)),
            Some(value),
            "callsite argument proof must travel through FunctionFacts, not r2dec local inference"
        );
        assert_eq!(
            facts
                .callsites()
                .and_then(|callsites| callsites.arguments_for_site(callsite))
                .and_then(|args| args.register_argument_locations.first())
                .map(|location| (location.index, location.value, location.storage)),
            Some((
                0,
                value,
                r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
            )),
            "register argument location proof must travel through FunctionFacts"
        );
    }

    #[test]
    fn a_recovered_pointer_replaces_a_storage_width_scalar() {
        let existing = CTypeLike::Int {
            bits: 32,
            signedness: crate::Signedness::Signed,
        };
        let recovered = CTypeLike::Pointer(Box::new(CTypeLike::Void));
        assert!(recovered_type_outranks(
            &existing,
            &recovered,
            64,
            &crate::ExternalTypeDb::default()
        ));
    }

    #[test]
    fn a_recovered_type_never_demotes_a_structured_one() {
        let existing = CTypeLike::Pointer(Box::new(CTypeLike::Struct("Node".to_string())));
        for recovered in [
            CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Signed,
            },
            CTypeLike::Pointer(Box::new(CTypeLike::Void)),
            CTypeLike::Typedef("int64_t".to_string()),
        ] {
            assert!(
                !recovered_type_outranks(
                    &existing,
                    &recovered,
                    64,
                    &crate::ExternalTypeDb::default()
                ),
                "{recovered:?} must not replace a struct pointer"
            );
        }
    }

    #[test]
    fn a_recovered_type_that_renders_the_same_is_not_a_replacement() {
        let existing = CTypeLike::Typedef("int32_t".to_string());
        let recovered = CTypeLike::Int {
            bits: 32,
            signedness: crate::Signedness::Signed,
        };
        assert!(!recovered_type_outranks(
            &existing,
            &recovered,
            64,
            &crate::ExternalTypeDb::default()
        ));
    }

    #[test]
    fn a_storage_width_scalar_is_not_evidence_for_replacing_another_one() {
        let existing = CTypeLike::Int {
            bits: 64,
            signedness: crate::Signedness::Signed,
        };
        let recovered = CTypeLike::Int {
            bits: 32,
            signedness: crate::Signedness::Unsigned,
        };
        assert!(!recovered_type_outranks(
            &existing,
            &recovered,
            64,
            &crate::ExternalTypeDb::default()
        ));
    }

    #[test]
    fn certified_call_argument_projects_callee_pointer_type_to_caller_parameter() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let value = r2ssa::ValueId(11);
        let signed_byte = CTypeLike::Int {
            bits: 8,
            signedness: crate::Signedness::Signed,
        };
        let pointer = CTypeLike::Pointer(Box::new(signed_byte));
        let function_names = HashMap::from([(0x402000, "strlen".to_string())]);
        let symbols = HashMap::new();
        let known_function_signatures = HashMap::from([(
            "strlen".to_string(),
            crate::FunctionType {
                return_type: CTypeLike::Typedef("size_t".to_string()),
                params: vec![pointer.clone()],
                variadic: false,
            },
        )]);
        let callee_facts = BTreeMap::new();
        let identity_ctx = crate::CalleeIdentityContext {
            function_names: &function_names,
            symbols: &symbols,
            callee_facts: &callee_facts,
            known_function_signatures: &known_function_signatures,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x402000)], &identity_ctx);
        let callsites = FunctionCallsiteFacts {
            by_callsite: BTreeMap::from([(
                callsite,
                CallsiteArgumentFacts {
                    callsite,
                    call_site_id: r2ssa::CallSiteId(2),
                    at: r2ssa::InstId(5),
                    target: r2ssa::ValueId(10),
                    direct_target: Some(0x402000),
                    argument_values: vec![CallArgumentValueFact { index: 0, value }],
                    variadic: false,
                    fixed_argument_count: None,
                    callee_signature: None,
                    variadic_argument_count_evidence: None,
                    variadic_argument_count_refusal: None,
                    register_argument_locations: Vec::new(),
                    stack_argument_locations: Vec::new(),
                },
            )]),
        };
        let mut render = FunctionRenderFacts::default();
        render.certified_exprs.insert(
            r2ssa::SemanticId::expression(value),
            CertifiedExpr {
                id: r2ssa::SemanticId::expression(value),
                fact: ExpressionRenderFact {
                    value,
                    defining_inst: Some(r2ssa::InstId(4)),
                    width: 8,
                    renderable: true,
                },
                inputs: Vec::new(),
                bindings: BTreeSet::from([r2ssa::SemanticId::Parameter(0)]),
                guarded_phi: None,
            },
        );
        let signature = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg0".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: crate::Signedness::Signed,
                }),
            }],
        };
        let mut facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature.clone()),
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &signature,
                    [crate::SignatureCertificateSource::LocalInference],
                ),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_callee_resolution(resolution)
        .with_callsites(callsites)
        .with_render(render);

        assert_eq!(facts.apply_certified_call_argument_type_constraints(64), 1);
        let typed = facts
            .type_facts()
            .render_authorized_signature()
            .and_then(|signature| signature.params[0].ty.as_ref());
        assert_eq!(typed, Some(&pointer));
        assert!(
            facts
                .type_facts()
                .signature_certificate
                .as_ref()
                .is_some_and(|certificate| certificate
                    .sources
                    .contains(&crate::SignatureCertificateSource::CalleeSignature))
        );
    }

    #[test]
    fn function_facts_owns_canonical_call_render_disposition() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let target = r2ssa::ValueId(10);
        let arg = r2ssa::ValueId(11);
        let render = FunctionCallRenderFacts {
            by_callsite: BTreeMap::from([(
                callsite,
                CallsiteRenderFact {
                    callsite,
                    target: Some(target),
                    disposition: CallsiteRenderDisposition::AssignedResult,
                    proof_values: vec![arg],
                    residual_reason: None,
                },
            )]),
        };

        let facts = FunctionFacts::default().with_call_render(render);

        let fact = facts
            .call_render()
            .and_then(|render| render.fact_for_site(callsite))
            .expect("call render fact must travel through FunctionFacts");
        assert_eq!(fact.target, Some(target));
        assert_eq!(fact.disposition, CallsiteRenderDisposition::AssignedResult);
        assert_eq!(fact.proof_values, vec![arg]);
    }

    #[test]
    fn callsite_facts_own_canonical_argument_vector() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let register_value = r2ssa::ValueId(11);
        let stack_value = r2ssa::ValueId(12);
        let duplicate_stack_value = r2ssa::ValueId(99);
        let args = CallsiteArgumentFacts {
            callsite,
            call_site_id: r2ssa::CallSiteId(2),
            at: r2ssa::InstId(5),
            target: r2ssa::ValueId(10),
            direct_target: Some(0x402000),
            argument_values: vec![CallArgumentValueFact {
                index: 0,
                value: register_value,
            }],
            variadic: false,
            fixed_argument_count: None,
            callee_signature: None,
            variadic_argument_count_evidence: None,
            variadic_argument_count_refusal: None,
            register_argument_locations: vec![RegisterCallArgumentLocationFact {
                index: 0,
                value: register_value,
                storage: r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
                source_inst: Some(r2ssa::InstId(4)),
            }],
            stack_argument_locations: vec![
                StackCallArgumentLocationFact {
                    index: 0,
                    value: duplicate_stack_value,
                    object: r2ssa::ObjectId(1),
                    offset: 0x20,
                    memory_access: r2ssa::StructuredAccessId {
                        inst: r2ssa::InstId(3),
                        ordinal: 0,
                    },
                    source_inst: Some(r2ssa::InstId(3)),
                },
                StackCallArgumentLocationFact {
                    index: 1,
                    value: stack_value,
                    object: r2ssa::ObjectId(2),
                    offset: 0x28,
                    memory_access: r2ssa::StructuredAccessId {
                        inst: r2ssa::InstId(4),
                        ordinal: 0,
                    },
                    source_inst: Some(r2ssa::InstId(4)),
                },
            ],
        };

        assert_eq!(
            args.canonical_argument_values(),
            vec![register_value, stack_value],
            "canonical callsite argument ordering and stack fallback must be owned by r2types"
        );
    }

    #[test]
    fn function_facts_owns_canonical_call_results() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let value = r2ssa::ValueId(21);
        let derived_value = r2ssa::ValueId(22);
        let owner = r2ssa::ValueOwner::StackSlot {
            object: r2ssa::ObjectId(3),
            offset: -8,
        };
        let call_results = FunctionCallResultFacts {
            by_value: BTreeMap::from([
                (
                    value,
                    CallResultFact {
                        callsite,
                        call_site_id: r2ssa::CallSiteId(2),
                        at: r2ssa::InstId(8),
                        value,
                        width: 8,
                        relation: r2ssa::CallResultValueRelation::Identity,
                        carrier: r2ssa::ReturnCarrier::Register {
                            storage: r2ssa::CanonicalStorageId {
                                space: r2ssa::CanonicalStorageSpace::Register,
                                offset: 0x10,
                                size: 8,
                            },
                        },
                        owner: Some(owner.clone()),
                    },
                ),
                (
                    derived_value,
                    CallResultFact {
                        callsite,
                        call_site_id: r2ssa::CallSiteId(2),
                        at: r2ssa::InstId(9),
                        value: derived_value,
                        width: 4,
                        relation: r2ssa::CallResultValueRelation::Derived,
                        carrier: r2ssa::ReturnCarrier::Register {
                            storage: r2ssa::CanonicalStorageId {
                                space: r2ssa::CanonicalStorageSpace::Register,
                                offset: 0x10,
                                size: 4,
                            },
                        },
                        owner: Some(r2ssa::ValueOwner::StackSlot {
                            object: r2ssa::ObjectId(4),
                            offset: -4,
                        }),
                    },
                ),
            ]),
            by_callsite: BTreeMap::from([(callsite, vec![value, derived_value])]),
        };

        let facts = FunctionFacts::default().with_call_results(call_results);

        assert_eq!(
            facts
                .call_results()
                .and_then(|results| results.result_for_value(value))
                .and_then(|result| result.owner.as_ref()),
            Some(&owner),
            "call-result ownership proof must travel through FunctionFacts, not r2dec local inference"
        );
        assert_eq!(
            facts
                .call_results()
                .and_then(|results| results.owner_for_site(callsite)),
            Some(&owner),
            "derived values must not replace the identity result's stable owner"
        );
        assert_eq!(
            facts
                .call_results()
                .map(|results| results.results_for_site(callsite).count()),
            Some(2),
            "call-result site index must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .call_results()
                .and_then(|results| results.owner_for_site(callsite)),
            Some(&owner),
            "call-result owner lookup must be available by callsite"
        );
    }

    #[test]
    fn call_result_definition_is_not_replaced_by_a_later_stack_owner() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let defined = r2ssa::ValueId(20);
        let stored = r2ssa::ValueId(21);
        let storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0x10,
            size: 8,
        };
        let stack_owner = r2ssa::ValueOwner::StackSlot {
            object: r2ssa::ObjectId(3),
            offset: -8,
        };
        let call_results = FunctionCallResultFacts {
            by_value: BTreeMap::from([
                (
                    defined,
                    CallResultFact {
                        callsite,
                        call_site_id: r2ssa::CallSiteId(2),
                        at: r2ssa::InstId(8),
                        value: defined,
                        width: 8,
                        relation: r2ssa::CallResultValueRelation::Identity,
                        carrier: r2ssa::ReturnCarrier::Register { storage },
                        owner: Some(r2ssa::ValueOwner::Value(defined)),
                    },
                ),
                (
                    stored,
                    CallResultFact {
                        callsite,
                        call_site_id: r2ssa::CallSiteId(2),
                        at: r2ssa::InstId(9),
                        value: stored,
                        width: 8,
                        relation: r2ssa::CallResultValueRelation::Identity,
                        carrier: r2ssa::ReturnCarrier::Register { storage },
                        owner: Some(stack_owner.clone()),
                    },
                ),
            ]),
            by_callsite: BTreeMap::from([(callsite, vec![defined, stored])]),
        };

        assert_eq!(
            call_results
                .definition_for_site(callsite)
                .map(|result| result.value),
            Some(defined),
            "the call statement must keep the boundary definition the binding plan can spell"
        );
        assert_eq!(
            call_results.owner_for_site(callsite),
            Some(&stack_owner),
            "the later stable owner remains available for subsequent result flow"
        );
    }

    #[test]
    fn prepared_call_results_bind_certified_exprs_to_stable_call_ids() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x402000, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
            val: Varnode::register(0x00, 8),
        });
        let result_storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let target_storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Constant,
            offset: 0x402000,
            size: 8,
        };
        let call_interface = r2ssa::SourceCallSiteInterface::new(
            b"certified-call-result-fixture".to_vec(),
            r2ssa::SourceCallSiteIdentity::new(0x401000, 0, target_storage),
            true,
            "sysv64",
            [],
            false,
            false,
            r2ssa::SourceCallResult::Register {
                storage: result_storage,
            },
        )
        .expect("exact call-result interface");
        let prepared = r2ssa::SsaArtifact::for_decompile_with_interfaces(
            &[block],
            Some(&x86_stack_home_arch()),
            None,
            vec![call_interface],
        )
        .expect("prepared exact call-result fixture");
        let mut facts = FunctionFacts::default();
        facts.attach_prepared_decompile_evidence(&prepared);

        let store_value = prepared
            .function()
            .get_block(0x401000)
            .expect("entry block")
            .ops
            .iter()
            .find_map(|op| match op {
                r2ssa::SSAOp::Store { val, .. } => prepared.graph().value_id_for_var(val),
                _ => None,
            })
            .expect("stored call result");
        let result = facts
            .call_results()
            .and_then(|results| results.result_for_value(store_value))
            .expect("canonical call-result fact");
        let binding = r2ssa::SemanticId::call(result.call_site_id);
        let certified = facts
            .render()
            .and_then(|render| render.certified_expr_for_value(store_value))
            .expect("certified call-result expression");

        assert!(certified.fact.renderable);
        assert!(certified.bindings.contains(&binding));
    }

    #[test]
    fn an_implicit_call_read_keeps_its_entry_value_as_a_certified_parameter() {
        let mut block = R2ILBlock::new(0x401000, 4);
        let target = Varnode::constant(0x402000, 8);
        block.push(R2ILOp::Call {
            target: target.clone(),
        });
        let register_storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let revision = b"implicit-call-parameter".to_vec();
        let parameter_storage = register_storage(0x10);
        let function_interface = r2ssa::SourceFunctionInterface::new_exact(
            revision.clone(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(0, parameter_storage)],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0x28)))
        .expect("exact caller interface");
        let logical_parameter = r2ssa::SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32),
        );
        let callee_interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            revision.clone(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(0, parameter_storage)],
            r2ssa::SourceFunctionReturn::Void,
            [],
            [logical_parameter],
            None,
            Some(
                r2ssa::SourceTypeGraph::new(
                    [r2ssa::SourceType::new(
                        0,
                        r2ssa::SourceTypeKind::UnsignedInteger,
                        32,
                        32,
                    )],
                    [],
                )
                .expect("callee type graph"),
            ),
        )
        .expect("logical callee interface");
        let call_interface = r2ssa::SourceCallSiteInterface::new(
            revision,
            r2ssa::SourceCallSiteIdentity::new(
                0x401000,
                0,
                r2ssa::CanonicalStorageId::from_varnode(&target),
            ),
            true,
            "sysv64",
            [r2ssa::SourceCallArgumentSpec::new(0, parameter_storage)],
            false,
            false,
            r2ssa::SourceCallResult::Void,
        )
        .and_then(|interface| interface.with_exact_callee_interface(callee_interface.clone()))
        .expect("exact callee interface");
        let prepared = r2ssa::SsaArtifact::for_decompile_with_interfaces(
            &[block],
            Some(&x86_stack_home_arch()),
            Some(function_interface),
            vec![call_interface],
        )
        .expect("prepared implicit-call fixture");
        let parameter = prepared
            .facts()
            .boundaries
            .parameters
            .get(&0)
            .expect("entry parameter boundary");
        assert!(prepared.graph().use_sites(parameter.value).is_empty());
        assert_eq!(
            prepared
                .callsite_certificate_for_op(0x401000, 0)
                .expect("callsite certificate")
                .argument_values,
            [parameter.value]
        );

        let mut facts = FunctionFacts::default();
        facts.attach_prepared_decompile_evidence(&prepared);
        let callsite = CallsiteKey {
            block_addr: 0x401000,
            op_index: 0,
        };
        assert_eq!(
            facts
                .callsites()
                .and_then(|facts| facts.arguments_for_site(callsite))
                .and_then(|facts| facts.callee_signature.as_ref()),
            None,
            "an exact carrier interface does not prove the callee's C signedness"
        );

        let callee_source = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &[R2ILBlock::new(0x402000, 4)],
                Some(&x86_stack_home_arch()),
                callee_interface,
            )
            .expect("prepared callee owner"),
        );
        let signed_signature = crate::FunctionType {
            return_type: CTypeLike::Void,
            params: vec![CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            }],
            variadic: false,
        };
        let source_owned_signature =
            SourceOwnedCalleeSignature::new(callee_source, signed_signature.clone())
                .expect("logical type fits the exact low-bit carrier");
        facts.apply_source_owned_callee_signatures(
            &prepared,
            &BTreeMap::from([(0x402000, source_owned_signature)]),
        );
        assert_eq!(
            facts
                .callsites()
                .and_then(|facts| facts.arguments_for_site(callsite))
                .and_then(|facts| facts.callee_signature.as_ref()),
            Some(&signed_signature),
            "only the retained callee body may add logical signedness"
        );
        facts.populate_certified_parameter_exprs(&prepared, &x86_stack_home_param_slots(&prepared));

        assert_eq!(
            facts
                .render()
                .expect("render facts")
                .parameter_values(0)
                .collect::<Vec<_>>(),
            [parameter.value]
        );
    }

    #[test]
    fn prepared_decompile_evidence_replaces_detached_source_dependent_rows() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x402000, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let callsite = CallsiteKey {
            block_addr: 0x401000,
            op_index: 0,
        };
        let sentinel_value = r2ssa::ValueId(0xfeed);
        let sentinel_callsite = CallsiteArgumentFacts {
            callsite,
            call_site_id: r2ssa::CallSiteId(0xbeef),
            at: r2ssa::InstId(0xbeef),
            target: sentinel_value,
            direct_target: Some(0x5555),
            argument_values: vec![CallArgumentValueFact {
                index: 0,
                value: sentinel_value,
            }],
            variadic: false,
            fixed_argument_count: None,
            callee_signature: None,
            variadic_argument_count_evidence: None,
            variadic_argument_count_refusal: None,
            register_argument_locations: Vec::new(),
            stack_argument_locations: Vec::new(),
        };
        let sentinel_render = CallsiteRenderFact {
            callsite,
            target: Some(sentinel_value),
            disposition: CallsiteRenderDisposition::Residualized,
            proof_values: vec![sentinel_value],
            residual_reason: Some("upstream refusal".to_string()),
        };
        let string_value = r2ssa::ValueId(0xcafe);
        let member_op = (0x501000, 3, false);
        let member_access = MemberAccessRenderFact {
            access: r2ssa::StructuredAccessId {
                inst: r2ssa::InstId(7),
                ordinal: 0,
            },
            block_addr: member_op.0,
            op_index: member_op.1,
            object: r2ssa::ObjectId(9),
            is_write: false,
            field_offset: 8,
            field_name: "len".to_string(),
            field_type: None,
            access_width: 32,
        };
        let existing_render = FunctionRenderFacts {
            string_literals_by_value: BTreeMap::from([(
                string_value,
                StringLiteralRenderFact {
                    value: string_value,
                    address: 0x600000,
                    text: "existing".to_string(),
                    source: StringLiteralRenderSource::TypedFunctionFacts,
                },
            )]),
            member_accesses_by_op: BTreeMap::from([(member_op, vec![member_access.clone()])]),
            ..FunctionRenderFacts::default()
        };
        let mut facts = FunctionFacts::default()
            .with_callsites(FunctionCallsiteFacts {
                by_callsite: BTreeMap::from([(callsite, sentinel_callsite.clone())]),
            })
            .with_call_render(FunctionCallRenderFacts {
                by_callsite: BTreeMap::from([(callsite, sentinel_render.clone())]),
            })
            .with_render(existing_render);

        facts.attach_prepared_decompile_evidence(&prepared);

        assert_ne!(
            facts
                .callsites()
                .and_then(|callsites| callsites.arguments_for_site(callsite)),
            Some(&sentinel_callsite),
            "a detached callsite row must not outrank the retained prepared artifact"
        );
        assert_ne!(
            facts
                .call_render()
                .and_then(|render| render.fact_for_site(callsite)),
            Some(&sentinel_render),
            "a detached call-render disposition must not outrank the retained prepared artifact"
        );
        assert!(
            facts
                .render()
                .and_then(|render| render.string_literal_for_value(string_value))
                .is_none(),
            "an unvalidated detached string annotation must be removed during source rebuild"
        );
        assert!(
            facts
                .render()
                .and_then(|render| render.member_accesses_by_op.get(&member_op))
                .is_none(),
            "an unvalidated detached member projection must be removed during source rebuild"
        );
        assert!(
            facts
                .callee_resolution()
                .and_then(|resolution| resolution.identity_for_callsite(callsite))
                .is_some(),
            "prepared evidence should still fill missing FunctionFacts groups"
        );
    }

    #[test]
    fn source_owned_seal_rederives_render_call_and_control_facts() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x402000, 8),
        });
        let source = Arc::new(
            r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
                .expect("prepared source-owned seal fixture"),
        );
        let canonical_report = || {
            let mut report =
                FunctionFacts::default().with_assumptions(source.facts().assumptions.clone());
            SourceOwnedFunctionFacts::enrich_report_from_source_for_decompile(
                source.as_ref(),
                &mut report,
            );
            report
        };

        assert!(
            SourceOwnedFunctionFacts::seal(Arc::clone(&source), canonical_report()).is_some(),
            "the independently rederived canonical report must seal"
        );

        let mut forged_render = canonical_report();
        forged_render
            .render
            .certified_exprs
            .values_mut()
            .next()
            .expect("fixture certified expression")
            .fact
            .width = 1;
        assert!(
            SourceOwnedFunctionFacts::seal(Arc::clone(&source), forged_render).is_none(),
            "a detached render-core mutation must not validate against itself"
        );

        let mut forged_call = canonical_report();
        assert!(!forged_call.call_render.by_callsite.is_empty());
        forged_call.call_render.by_callsite.clear();
        assert!(
            SourceOwnedFunctionFacts::seal(Arc::clone(&source), forged_call).is_none(),
            "a detached call-render mutation must not validate against itself"
        );

        let mut forged_control = canonical_report();
        assert!(!forged_control.control.control_domains.by_block.is_empty());
        forged_control.control = FunctionControlFacts::default();
        assert!(
            SourceOwnedFunctionFacts::seal(source, forged_control).is_none(),
            "a detached control projection must not validate against itself"
        );
    }

    #[test]
    fn field_certificates_populate_direct_member_render_facts() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        let render = facts.render().expect("prepared render facts");
        let member = render
            .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
            .expect("typed member render fact");
        let expected = CTypeLike::Int {
            bits: 64,
            signedness: crate::model::Signedness::Unsigned,
        };
        assert_eq!(member.field_type.as_ref(), Some(&expected));
        assert_eq!(render.memory_value_type(member.access), Some(&expected));
    }

    #[test]
    fn field_certificates_follow_loop_carried_parameter_phi() {
        let mut entry = R2ILBlock::new(0x400ff0, 0x10);
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x401000, 8),
        });
        let mut header = R2ILBlock::new(0x401000, 0x10);
        header.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        header.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        header.push(R2ILOp::CBranch {
            target: Varnode::constant(0x401020, 8),
            cond: Varnode::register(0x80, 1),
        });
        let mut latch = R2ILBlock::new(0x401010, 0x10);
        latch.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x200, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0x10, 8),
        });
        latch.push(R2ILOp::Load {
            dst: Varnode::register(0x10, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x200, 8),
        });
        latch.push(R2ILOp::Branch {
            target: Varnode::constant(0x401000, 8),
        });
        let mut exit = R2ILBlock::new(0x401020, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0x08, 8),
        });
        let prepared = x86_stack_home_prepared(&[entry, header, latch, exit]);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![
                crate::facts::FieldAccessCertificate {
                    slot: 0,
                    field_offset: 8,
                    field_name: "value".to_string(),
                    field_type: Some("uint64_t".to_string()),
                },
                crate::facts::FieldAccessCertificate {
                    slot: 0,
                    field_offset: 0x10,
                    field_name: "next".to_string(),
                    field_type: Some("struct Node *".to_string()),
                },
            ],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        let upstream_carrier = prepared
            .structured()
            .loops
            .values()
            .flat_map(|loop_fact| loop_fact.carriers.iter())
            .next()
            .expect("prepared loop carrier");
        let projected_carrier = facts
            .render()
            .and_then(|render| render.certified_entities.get(&upstream_carrier.id))
            .expect("projected loop carrier");
        assert!(matches!(
            projected_carrier,
            CertifiedEntity::LoopCarrier {
                entries,
                updates,
                dominating_initializers,
                members,
                ..
            } if entries == &upstream_carrier.entries
                && updates == &upstream_carrier.updates
                && dominating_initializers == &upstream_carrier.dominating_initializers
                && members == &upstream_carrier.members
        ));
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );
        facts.populate_certified_loop_carrier_types();

        assert!(facts.render().is_some_and(|render| {
            render
                .member_access_for_op(0x401000, 1, false, "value", 8, Some(8))
                .is_some()
                && render
                    .member_access_for_op(0x401010, 1, false, "next", 0x10, Some(8))
                    .is_some()
        }));
        let expected = CTypeLike::Pointer(Box::new(CTypeLike::Struct("Node".to_string())));
        assert!(facts.render().is_some_and(|render| {
            render.loop_carriers().any(|carrier| {
                matches!(
                    carrier,
                    CertifiedEntity::LoopCarrier { ty: Some(ty), .. } if *ty == expected
                )
            })
        }));
    }

    #[test]
    fn field_certificates_do_not_populate_member_render_facts_for_wrong_width() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "small".to_string(),
                field_type: Some("uint32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "small", 8, Some(8))
                .is_none()),
            "wrong-width field certificate must not authorize member rendering"
        );
    }

    #[test]
    fn field_certificates_do_not_populate_member_render_facts_for_wrong_param_slot() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x18, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_none()),
            "a field certificate for one parameter slot must not authorize the same offset on another parameter"
        );

        let matching_type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 1,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut matching_facts = FunctionFacts::new(matching_type_facts, None);

        matching_facts.attach_prepared_decompile_evidence(&prepared);
        matching_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        assert!(
            matching_facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_some()),
            "the same memory proof should authorize the certificate for the matching parameter slot"
        );
    }

    fn x86_stack_home_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rax", 0x00, 8));
        arch.add_register(RegisterDef::sub("eax", 0x00, 4, "rax"));
        arch.add_register(RegisterDef::new("rdi", 0x10, 8));
        arch.add_register(RegisterDef::new("rsi", 0x18, 8));
        arch.add_register(RegisterDef::sub("esi", 0x18, 4, "rsi"));
        arch.add_register(RegisterDef::new("rbp", 0x20, 8));
        arch.add_register(RegisterDef::new("rsp", 0x28, 8));
        arch.add_register(RegisterDef::new("rip", 0x30, 8));
        arch
    }

    fn x86_stack_home_prepared(blocks: &[R2ILBlock]) -> r2ssa::SsaArtifact {
        let register_storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let frame_pointer = register_storage(0x20);
        let parameter = register_storage(0x10);
        let second_parameter = register_storage(0x18);
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"x86-stack-home-fixture".to_vec(),
            "sysv64",
            [
                r2ssa::SourceAbiParameterSpec::new(0, parameter),
                r2ssa::SourceAbiParameterSpec::new(1, second_parameter),
            ],
            r2ssa::SourceFunctionReturn::Register {
                storage: register_storage(0x00),
            },
            [r2ssa::SourceStackSlotSpec::new_parameter_home(
                r2ssa::StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
                0,
                parameter,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0x28)))
        .and_then(|interface| interface.with_frame_pointer_storage(frame_pointer))
        .expect("exact x86 stack-home interface");
        r2ssa::SsaArtifact::for_decompile_with_interface(
            blocks,
            Some(&x86_stack_home_arch()),
            interface,
        )
        .expect("prepared exact stack-home fixture")
    }

    fn x86_stack_home_param_slots(prepared: &r2ssa::SsaArtifact) -> ParamSlotResolver {
        exact_source_param_slot_resolver(prepared).expect("exact source parameter slots")
    }

    #[test]
    fn prepared_render_facts_certify_params_stack_memory_and_returns_by_semantic_id() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(0xffff_ffff_ffff_fff8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
            val: Varnode::register(0x10, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0x00, 8),
            a: Varnode::register(0x00, 8),
            b: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let signature = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Unsigned,
            }),
            params: vec![FunctionParamSpec {
                name: "buffer".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: crate::Signedness::Unsigned,
                }),
            }],
        };
        let mut facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature.clone()),
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &signature,
                    [crate::SignatureCertificateSource::ExternalContext],
                ),
                ..FunctionTypeFacts::default()
            },
            None,
        );
        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_certified_parameter_exprs(&prepared, &x86_stack_home_param_slots(&prepared));
        let render = facts.render().expect("certified render facts");

        let rdi = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.eq_ignore_ascii_case("rdi") && value.var.version == 0)
            .expect("entry rdi value");
        let param_id = r2ssa::SemanticId::parameter(0).expect("parameter ID");
        assert!(
            render
                .certified_expr_for_value(rdi.id)
                .is_some_and(|expr| expr.bindings.contains(&param_id)),
            "entry parameter binding must use ABI slot identity"
        );
        assert!(render.parameter_values(0).any(|value| value == rdi.id));
        assert_eq!(
            render
                .certified_entities
                .values()
                .filter(|entity| matches!(entity, CertifiedEntity::Parameter { .. }))
                .count(),
            1
        );
        let reloaded = prepared
            .certificates()
            .stack_reloads
            .values()
            .find(|reload| reload.canonical_source == rdi.id)
            .expect("certified parameter-home reload");
        assert!(
            render
                .certified_expr_for_value(reloaded.value)
                .is_some_and(|expr| expr.bindings.contains(&param_id)),
            "parameter identity must cross its certified stack-home reload"
        );
        assert!(
            render
                .certified_effects
                .values()
                .filter_map(CertifiedEffect::memory_fact)
                .find(|fact| fact.access == reloaded.load_access)
                .is_some_and(|fact| !fact.materialize_result),
            "a certified stack-home reload must render through its stable identity even when the raw value has multiple expression uses"
        );
        assert!(
            render
                .certified_exprs
                .values()
                .all(|expr| !expr.bindings.contains(&r2ssa::SemanticId::Parameter(1))),
            "unused ABI entry registers beyond signature arity must not become parameters"
        );

        let certified_entities = render.certified_entities.len();
        let memory_effects = render
            .certified_effects
            .values()
            .filter(|effect| {
                matches!(
                    effect.kind(),
                    CertifiedEffectKind::MemoryRead | CertifiedEffectKind::MemoryWrite
                )
            })
            .count();
        let return_effects = render
            .certified_effects
            .values()
            .filter(|effect| effect.kind() == CertifiedEffectKind::Return)
            .count();
        assert_eq!(certified_entities, 3);
        assert!(
            render
                .certified_entities
                .values()
                .any(|entity| matches!(entity, CertifiedEntity::Parameter { slot: 0, .. }))
        );
        assert!(
            render
                .certified_entities
                .values()
                .any(|entity| matches!(entity, CertifiedEntity::StackSlot { offset: -8, .. }))
        );
        assert_eq!(memory_effects, 2);
        assert!(return_effects >= 1);
        assert!(render.return_effect_id_for_op(0x401000, 4).is_some());
        assert!(render.return_for_op(0x401000, 4).is_some());
    }

    #[test]
    fn prepared_render_facts_certify_branch_guarded_phi() {
        let mut entry = R2ILBlock::new(0x401000, 4);
        entry.push(R2ILOp::IntEqual {
            dst: Varnode::unique(0x300, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x401008, 8),
            cond: Varnode::unique(0x300, 1),
        });
        let mut when_false = R2ILBlock::new(0x401004, 4);
        when_false.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(1, 8),
        });
        when_false.push(R2ILOp::Branch {
            target: Varnode::constant(0x40100c, 8),
        });
        let mut when_true = R2ILBlock::new(0x401008, 4);
        when_true.push(R2ILOp::Branch {
            target: Varnode::constant(0x40100c, 8),
        });
        let mut exit = R2ILBlock::new(0x40100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0x10, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(
            &[entry, when_false, when_true, exit],
            Some(&x86_stack_home_arch()),
        )
        .expect("prepared");
        let phi = prepared
            .function()
            .get_block(0x40100c)
            .and_then(|block| block.phis.iter().find(|phi| phi.dst.name == "rdi"))
            .and_then(|phi| prepared.graph().value_id_for_var(&phi.dst))
            .expect("return phi");
        let render = FunctionRenderFacts::from_prepared(&prepared);
        let guarded = render.guarded_phi_for_value(phi).expect("guarded phi");

        assert_eq!(
            guarded.predicate,
            r2ssa::SemanticId::predicate(r2ssa::PredicateId(0))
        );
        let r2ssa::SemanticId::Expression(true_value) = guarded.when_true.rendered else {
            panic!("guarded phi arm must render an expression identity");
        };
        assert_eq!(
            prepared.value_var(true_value),
            Some(&r2ssa::SSAVar::constant(0, 8)),
            "the true equality edge should substitute the proven constant"
        );
        assert_eq!(guarded.when_false.sources.len(), 1);
        assert_eq!(guarded.when_false.rendered, guarded.when_false.sources[0]);
    }

    #[test]
    fn prepared_render_facts_materialize_load_for_distinct_consumers() {
        let mut block = R2ILBlock::new(0x402000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(0x10, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
            val: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
            val: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let render = FunctionRenderFacts::from_prepared(&prepared);
        let read = render
            .memory_accesses()
            .find(|fact| !fact.is_write)
            .expect("certified load");

        assert!(
            read.materialize_result,
            "one certified load consumed by two rendered stores must be evaluated once"
        );
    }

    #[test]
    fn prepared_render_facts_keep_single_consumer_load_inline() {
        let mut block = R2ILBlock::new(0x402000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(0x10, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
            val: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let render = FunctionRenderFacts::from_prepared(&prepared);
        let read = render
            .memory_accesses()
            .find(|fact| !fact.is_write)
            .expect("certified load");

        assert!(
            !read.materialize_result,
            "a single rendered consumer should keep the load inline"
        );
    }

    #[test]
    fn parameter_identity_is_distinct_from_single_parameter_dependency() {
        let mut block = R2ILBlock::new(0x402000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::register(0x10, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x108, 8),
            a: Varnode::unique(0x100, 8),
            b: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::unique(0x108, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let mut facts = FunctionFacts::default();
        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_certified_parameter_exprs(&prepared, &x86_stack_home_param_slots(&prepared));
        let render = facts.render().expect("render facts");
        let copied = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name == "tmp:100")
            .expect("same-width parameter copy");
        let derived = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name == "tmp:108")
            .expect("derived expression");

        assert_eq!(render.exact_parameter_slot_for_value(copied.id), Some(0));
        assert_eq!(render.exact_parameter_slot_for_value(derived.id), None);
        assert_eq!(
            render.unique_parameter_dependency_slot_for_value(derived.id),
            Some(0)
        );
    }

    fn member_load_prepared_for_register(
        arch: &ArchSpec,
        register_offset: u64,
    ) -> r2ssa::SsaArtifact {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(register_offset, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        r2ssa::SsaArtifact::for_decompile(&[block], Some(arch)).expect("prepared")
    }

    fn field_certificate_type_facts(slot: usize, offset: u64) -> FunctionTypeFacts {
        FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot,
                field_offset: offset,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        }
    }

    #[test]
    fn field_certificates_fail_closed_without_param_slot_resolver() {
        let prepared = member_load_prepared_for_register(&x86_stack_home_arch(), 0x10);
        let mut facts = FunctionFacts::new(field_certificate_type_facts(0, 8), None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &ParamSlotResolver::default(),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_none()),
            "missing ABI slot evidence must not guess rdi as parameter slot 0"
        );
    }

    fn stack_home_field_load_prepared(with_store: bool) -> r2ssa::SsaArtifact {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(0xffff_ffff_ffff_fff8, 8),
        });
        if with_store {
            block.push(R2ILOp::Copy {
                dst: Varnode::unique(0x104, 8),
                src: Varnode::register(0x10, 8),
            });
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x100, 8),
                val: Varnode::unique(0x104, 8),
            });
        }
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x108, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(0xffff_ffff_ffff_fff8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x110, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x108, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x118, 8),
            a: Varnode::unique(0x110, 8),
            b: Varnode::constant(4, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x118, 8),
        });
        x86_stack_home_prepared(&[block])
    }

    #[test]
    fn field_certificates_populate_stack_home_member_render_facts() {
        let prepared = stack_home_field_load_prepared(true);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 4,
                field_name: "hash".to_string(),
                field_type: Some("uint32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        assert!(
            facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 6, false, "hash", 4, Some(4))
                .is_some()),
            "field certificate plus prepared stack-reload proof must authorize O0 stack-home member rendering"
        );
    }

    #[test]
    fn field_certificates_do_not_populate_stack_home_member_without_reload_proof() {
        let prepared = stack_home_field_load_prepared(false);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 4,
                field_name: "hash".to_string(),
                field_type: Some("uint32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 4, false, "hash", 4, Some(4))
                .is_none()),
            "field certificate must not authorize a member render through an unproven stack load"
        );
    }

    #[test]
    fn scalar_array_candidates_populate_indexed_member_render_facts() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntZExt {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::register(0x18, 4),
        });
        block.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x108, 8),
            a: Varnode::unique(0x100, 8),
            b: Varnode::constant(16, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x110, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::unique(0x108, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x118, 8),
            a: Varnode::unique(0x110, 8),
            b: Varnode::constant(4, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x118, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let index_value = prepared
            .memory_certificate_for_op_site(0x401000, 4, false)
            .expect("array load certificate")
            .address;
        let index_value = prepared
            .addresses()
            .parameter_expression(index_value)
            .and_then(|address| address.terms.first())
            .map(|term| term.value)
            .expect("semantic array index");
        let type_facts = FunctionTypeFacts {
            array_index_certificates: vec![crate::facts::ArrayIndexCertificate {
                slot: 0,
                base: Some(crate::facts::ArrayIndexBase::Param { index: 0 }),
                field_offset: 4,
                element_stride: 16,
            }],
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 4,
                field_name: "score".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            scalar_array_render_candidates: vec![crate::facts::ScalarArrayRenderCandidate {
                slot: 0,
                block_addr: 0x401000,
                op_index: 4,
                is_write: false,
                field_offset: 4,
                element_stride: 16,
                access_width: 4,
                index_value: Some(index_value),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_certified_parameter_exprs(&prepared, &x86_stack_home_param_slots(&prepared));
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );
        facts.populate_array_access_render_facts_from_scalar_candidates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );

        let render = facts.render().expect("render facts");
        assert!(
            render
                .member_access_for_op(0x401000, 4, false, "score", 4, Some(4))
                .is_some(),
            "scalar array candidate plus field certificate must authorize indexed member rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 4, 16, Some(4))
                .is_some(),
            "scalar array candidate must still authorize array rendering"
        );
        let array = render
            .array_access_for_op(0x401000, 4, false, 4, 16, Some(4))
            .expect("stable array render fact");
        assert_eq!(array.base, Some(r2ssa::SemanticId::Parameter(0)));
        assert_eq!(
            array.index,
            Some(r2ssa::SemanticId::expression(index_value))
        );
    }

    #[test]
    fn scalar_array_member_candidate_requires_semantic_index_identity() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
        });
        let prepared = x86_stack_home_prepared(&[block]);
        let type_facts_for_slot = |slot| FunctionTypeFacts {
            array_index_certificates: vec![crate::facts::ArrayIndexCertificate {
                slot,
                base: Some(crate::facts::ArrayIndexBase::Param { index: slot }),
                field_offset: 4,
                element_stride: 16,
            }],
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot,
                field_offset: 4,
                field_name: "score".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            scalar_array_render_candidates: vec![crate::facts::ScalarArrayRenderCandidate {
                slot,
                block_addr: 0x401000,
                op_index: 0,
                is_write: false,
                field_offset: 4,
                element_stride: 16,
                access_width: 4,
                index_value: None,
            }],
            ..FunctionTypeFacts::default()
        };

        let mut wrong_slot_facts = FunctionFacts::new(type_facts_for_slot(0), None);
        wrong_slot_facts.attach_prepared_decompile_evidence(&prepared);
        wrong_slot_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );
        assert!(
            wrong_slot_facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 0, false, "score", 4, Some(4))
                .is_none()),
            "scalar-array member candidate from rsi must not render with a slot 0 certificate"
        );

        let mut matching_slot_facts = FunctionFacts::new(type_facts_for_slot(1), None);
        matching_slot_facts.attach_prepared_decompile_evidence(&prepared);
        matching_slot_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(&prepared),
        );
        assert!(
            matching_slot_facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 0, false, "score", 4, Some(4))
                .is_none()),
            "coordinate-only array candidates must not authorize member rendering"
        );
    }

    #[test]
    fn function_facts_owns_canonical_control_facts() {
        let branch = BranchPredicateFact {
            id: r2ssa::PredicateId(0),
            block_addr: 0x401000,
            condition: r2ssa::ValueId(31),
            comparison: Some(PredicateComparisonFact {
                kind: r2ssa::CompareKind::Equal,
                lhs: r2ssa::ValueId(32),
                rhs: r2ssa::ValueId(33),
            }),
            evaluated_comparison: None,
            render_comparison: Some(PredicateComparisonFact {
                kind: r2ssa::CompareKind::Equal,
                lhs: r2ssa::ValueId(32),
                rhs: r2ssa::ValueId(33),
            }),
            true_target: 0x401010,
            false_target: 0x401004,
        };
        let switch = SwitchSelectorFact {
            proof_node: r2ssa::ProofNodeId::switch_certificate(0x402000).to_string(),
            block_addr: 0x402000,
            selector: Some(r2ssa::ValueId(41)),
            cases: vec![(0, 0x402010), (1, 0x402020)],
            default: Some(0x402030),
        };
        let loop_fact = LoopStructureFact {
            loop_id: r2ssa::LoopId(2),
            proof_node: r2ssa::ProofNodeId::loop_certificate(0x403000, r2ssa::LoopId(2))
                .to_string(),
            header: 0x403000,
            condition: Some(branch.id),
            condition_value: Some(branch.condition),
            body: vec![0x403000, 0x403010],
            latches: vec![0x403010],
            exits: vec![0x403020],
            for_loop: None,
        };
        let control = FunctionControlFacts {
            branch_predicates: BTreeMap::from([(branch.block_addr, branch.clone())]),
            block_assumptions: BTreeMap::from([(
                branch.true_target,
                vec![ControlBlockAssumptionFact {
                    predecessor: branch.block_addr,
                    predicate: branch.id,
                    truth: true,
                }],
            )]),
            loops: BTreeMap::from([(loop_fact.loop_id, loop_fact.clone())]),
            switches: BTreeMap::from([(switch.block_addr, switch.clone())]),
            control_domains: r2ssa::ControlDomainFacts::default(),
        };

        let facts = FunctionFacts::default().with_control(control);

        assert_eq!(
            facts
                .control()
                .and_then(|control| control.branch_for_block(0x401000)),
            Some(&branch),
            "branch predicate proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .control()
                .map(|control| control.assumptions_for_block(0x401010).count()),
            Some(1),
            "block assumption proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .control()
                .map(|control| control.loops_for_header(0x403000).count()),
            Some(1),
            "loop structure proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .control()
                .and_then(|control| control.switch_for_block(0x402000)),
            Some(&switch),
            "switch selector proof must travel through FunctionFacts"
        );
    }

    #[test]
    fn function_facts_owns_canonical_render_facts() {
        let value = r2ssa::ValueId(51);
        let access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(7),
            ordinal: 0,
        };
        let object = r2ssa::ObjectId(3);
        let expression_id = r2ssa::SemanticId::expression(value);
        let memory_id = r2ssa::SemanticId::memory_access(access);
        let return_at = r2ssa::InstId(9);
        let return_id = r2ssa::SemanticId::return_value(return_at);
        let render = FunctionRenderFacts {
            certified_exprs: BTreeMap::from([(
                expression_id,
                CertifiedExpr {
                    id: expression_id,
                    fact: ExpressionRenderFact {
                        value,
                        defining_inst: Some(r2ssa::InstId(8)),
                        width: 8,
                        renderable: true,
                    },
                    inputs: Vec::new(),
                    bindings: BTreeSet::new(),
                    guarded_phi: None,
                },
            )]),
            certified_entities: BTreeMap::from([(
                r2ssa::SemanticId::stack_slot(object),
                CertifiedEntity::StackSlot {
                    id: r2ssa::SemanticId::stack_slot(object),
                    object,
                    base: r2ssa::StackAddressBase::FramePointer,
                    offset: -8,
                    size: None,
                    array_layout: r2ssa::StackArrayLayoutDisposition::NotIndexed,
                    source_slot: None,
                    callee_allocation: None,
                },
            )]),
            certified_effects: BTreeMap::from([
                (
                    memory_id,
                    CertifiedEffect::Memory {
                        id: memory_id,
                        fact: MemoryAccessRenderFact {
                            access,
                            block_addr: 0x401000,
                            op_index: 4,
                            space: r2il::SpaceId::Ram,
                            object,
                            address: r2ssa::ValueId(52),
                            value: Some(value),
                            is_write: true,
                            width: 8,
                            materialize_result: false,
                            control_domain: test_control_domain(),
                        },
                    },
                ),
                (
                    return_id,
                    CertifiedEffect::Return {
                        id: return_id,
                        at: return_at,
                        fact: ReturnValueRenderFact {
                            block_addr: 0x401010,
                            op_index: 2,
                            value,
                            width: 8,
                            overlays: Vec::new(),
                            control_domain: test_control_domain(),
                        },
                    },
                ),
            ]),
            return_effects_by_op: BTreeMap::from([((0x401010, 2), return_id)]),
            memory_effects_by_op: BTreeMap::from([((0x401000, 4, true), vec![memory_id])]),
            string_literals_by_value: BTreeMap::from([(
                value,
                StringLiteralRenderFact {
                    value,
                    address: 0x402000,
                    text: "value".to_string(),
                    source: StringLiteralRenderSource::TypedFunctionFacts,
                },
            )]),
            member_accesses_by_op: BTreeMap::from([(
                (0x401000, 4, true),
                vec![MemberAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    is_write: true,
                    field_offset: 0,
                    field_name: "value".to_string(),
                    field_type: None,
                    access_width: 8,
                }],
            )]),
            array_accesses_by_op: BTreeMap::from([(
                (0x401000, 4, true),
                vec![ArrayAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    is_write: true,
                    field_offset: 0,
                    element_stride: 8,
                    access_width: 8,
                    base: None,
                    index: None,
                }],
            )]),
        };

        let facts = FunctionFacts::default().with_render(render);

        assert!(
            facts
                .render()
                .is_some_and(|render| render.expression_is_renderable(value)),
            "expression renderability proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.string_literal_for_value(value))
                .map(|literal| (literal.address, literal.text.as_str())),
            Some((0x402000, "value")),
            "string literal render proof must travel through FunctionFacts"
        );
        assert!(
            facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 4, true, "value", 0, Some(8))
                .is_some()),
            "member access render proof must travel through FunctionFacts"
        );
        assert!(
            facts.render().is_some_and(|render| render
                .array_access_for_op(0x401000, 4, true, 0, 8, Some(8))
                .is_some()),
            "array access render proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| {
                    render.memory_access_for_op(0x401000, 4, true, r2il::SpaceId::Ram)
                })
                .map(|memory| (memory.access, memory.space, memory.value, memory.width)),
            Some((access, r2il::SpaceId::Ram, Some(value), 8)),
            "memory access proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.return_for_op(0x401010, 2))
                .map(|ret| (ret.value, ret.width)),
            Some((value, 8)),
            "return value proof must travel through FunctionFacts"
        );
        assert!(
            facts
                .render()
                .is_some_and(|render| render.has_stack_slot_offset(-8)),
            "stack-slot offset proof must travel through FunctionFacts"
        );
    }

    #[test]
    fn function_facts_authorizes_stack_owner_render_by_object_type_and_name() {
        let object = r2ssa::ObjectId(11);
        let facts = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![crate::VisibleBinding {
                    name: "local_buf".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: crate::Signedness::Unsigned,
                    }))),
                    kind: VisibleBindingKind::Local,
                    stack_slot: Some(StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: -8,
                    }),
                    param_index: None,
                    source_reg: None,
                }],
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::FramePointer,
            -8,
        )]));

        let authorization = facts
            .authorized_stack_slot_owner_render(object, -8, "LOCAL_BUF")
            .expect("typed visible binding plus exact render object should authorize owner");
        assert_eq!(authorization.object, object);
        assert_eq!(authorization.offset, -8);
        assert_eq!(authorization.name, "LOCAL_BUF");
        assert!(
            facts
                .authorized_stack_slot_owner_render(r2ssa::ObjectId(12), -8, "local_buf")
                .is_none(),
            "a matching offset must not authorize the wrong SSA object"
        );
    }

    #[test]
    fn function_render_facts_require_exact_array_access_identity() {
        let access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(7),
            ordinal: 0,
        };
        let other_access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(8),
            ordinal: 0,
        };
        let object = r2ssa::ObjectId(3);
        let value = r2ssa::ValueId(51);
        let memory_id = r2ssa::SemanticId::memory_access(access);
        let render = FunctionRenderFacts {
            certified_effects: BTreeMap::from([(
                memory_id,
                CertifiedEffect::Memory {
                    id: memory_id,
                    fact: MemoryAccessRenderFact {
                        access,
                        block_addr: 0x401000,
                        op_index: 4,
                        space: r2il::SpaceId::Ram,
                        object,
                        address: r2ssa::ValueId(52),
                        value: Some(value),
                        is_write: false,
                        width: 4,
                        materialize_result: false,
                        control_domain: test_control_domain(),
                    },
                },
            )]),
            memory_effects_by_op: BTreeMap::from([((0x401000, 4, false), vec![memory_id])]),
            array_accesses_by_op: BTreeMap::from([(
                (0x401000, 4, false),
                vec![ArrayAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    is_write: false,
                    field_offset: 0,
                    element_stride: 4,
                    access_width: 4,
                    base: None,
                    index: None,
                }],
            )]),
            ..FunctionRenderFacts::default()
        };

        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(4))
                .is_some(),
            "exact op/access/object/direction/width/stride identity should authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 5, false, 0, 4, Some(4))
                .is_none(),
            "wrong op site must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, true, 0, 4, Some(4))
                .is_none(),
            "wrong direction must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 4, 4, Some(4))
                .is_none(),
            "wrong field offset must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 0, 8, Some(4))
                .is_none(),
            "wrong stride must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(8))
                .is_none(),
            "wrong access width must not authorize array rendering"
        );

        let mut wrong_object = render.clone();
        wrong_object
            .array_accesses_by_op
            .get_mut(&(0x401000, 4, false))
            .expect("array fact")
            .first_mut()
            .expect("array fact")
            .object = r2ssa::ObjectId(9);
        assert!(
            wrong_object
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(4))
                .is_none(),
            "wrong object identity must not authorize array rendering"
        );

        let mut wrong_access = render.clone();
        wrong_access
            .array_accesses_by_op
            .get_mut(&(0x401000, 4, false))
            .expect("array fact")
            .first_mut()
            .expect("array fact")
            .access = other_access;
        assert!(
            wrong_access
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(4))
                .is_none(),
            "wrong memory-access identity must not authorize array rendering"
        );
    }

    #[test]
    fn memory_access_lookup_requires_exact_address_space() {
        let ram_access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(7),
            ordinal: 0,
        };
        let custom_access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(7),
            ordinal: 1,
        };
        let effect = |access, space| {
            let id = r2ssa::SemanticId::memory_access(access);
            (
                id,
                CertifiedEffect::Memory {
                    id,
                    fact: MemoryAccessRenderFact {
                        access,
                        block_addr: 0x401000,
                        op_index: 4,
                        space,
                        object: r2ssa::ObjectId(3),
                        address: r2ssa::ValueId(52),
                        value: Some(r2ssa::ValueId(51)),
                        is_write: false,
                        width: 4,
                        materialize_result: false,
                        control_domain: test_control_domain(),
                    },
                },
            )
        };
        let ram_id = r2ssa::SemanticId::memory_access(ram_access);
        let custom_id = r2ssa::SemanticId::memory_access(custom_access);
        let render = FunctionRenderFacts {
            certified_effects: BTreeMap::from([
                effect(ram_access, r2il::SpaceId::Ram),
                effect(custom_access, r2il::SpaceId::Custom(7)),
            ]),
            memory_effects_by_op: BTreeMap::from([((0x401000, 4, false), vec![ram_id, custom_id])]),
            ..FunctionRenderFacts::default()
        };

        assert_eq!(
            render
                .memory_access_for_op(0x401000, 4, false, r2il::SpaceId::Ram)
                .map(|fact| fact.access),
            Some(ram_access)
        );
        assert_eq!(
            render
                .memory_access_for_op(0x401000, 4, false, r2il::SpaceId::Custom(7))
                .map(|fact| fact.access),
            Some(custom_access)
        );
        assert!(
            render
                .memory_access_for_op(0x401000, 4, false, r2il::SpaceId::Custom(8))
                .is_none()
        );
    }

    #[test]
    fn function_facts_authorizes_recovered_stack_owner_only_by_exact_object_offset_and_name() {
        let object = r2ssa::ObjectId(21);
        let facts = FunctionFacts::default().with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::FramePointer,
            -4,
        )]));

        let authorization = facts
            .authorized_recovered_stack_slot_owner_render(object, -4, "i")
            .expect("a recovered loop scalar with exact object and offset should authorize");
        assert_eq!(authorization.object, object);
        assert_eq!(authorization.offset, -4);
        assert_eq!(authorization.name, "i");
        assert!(
            facts
                .authorized_recovered_stack_slot_owner_render(r2ssa::ObjectId(22), -4, "i")
                .is_none(),
            "wrong object must not authorize recovered stack owner rendering"
        );
        assert!(
            facts
                .authorized_recovered_stack_slot_owner_render(object, 4, "i")
                .is_none(),
            "wrong offset must not authorize recovered stack owner rendering"
        );
        for placeholder in ["fake_stack_slot", "local_4", "var_4h", "stack_8"] {
            assert!(
                facts
                    .authorized_recovered_stack_slot_owner_render(object, -4, placeholder)
                    .is_none(),
                "placeholder name {placeholder} must not authorize recovered stack owner rendering"
            );
        }
    }

    #[test]
    fn function_facts_authorizes_stack_param_owner_render_only_for_params() {
        let object = r2ssa::ObjectId(13);
        let facts = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![
                    crate::VisibleBinding {
                        name: "stack_arg".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Param,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: Some(6),
                        source_reg: None,
                    },
                    crate::VisibleBinding {
                        name: "local_alias".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Local,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: None,
                        source_reg: None,
                    },
                ],
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::StackPointer,
            8,
        )]));

        let authorization = facts
            .authorized_stack_param_owner_render(object, 8)
            .expect("typed parameter binding plus exact render object should authorize owner");
        assert_eq!(authorization.object, object);
        assert_eq!(authorization.offset, 8);
        assert_eq!(authorization.name, "stack_arg");
        assert!(
            facts
                .authorized_stack_param_owner_render(r2ssa::ObjectId(14), 8)
                .is_none(),
            "the stack parameter path still requires the exact render object"
        );
        assert!(
            facts
                .authorized_stack_param_owner_render(object, -8)
                .is_none(),
            "the stack parameter path still requires the exact offset"
        );

        let ambiguous = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![
                    crate::VisibleBinding {
                        name: "left".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Param,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: Some(6),
                        source_reg: None,
                    },
                    crate::VisibleBinding {
                        name: "right".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Param,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: Some(6),
                        source_reg: None,
                    },
                ],
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::StackPointer,
            8,
        )]));
        assert!(
            ambiguous
                .authorized_stack_param_owner_render(object, 8)
                .is_none(),
            "ambiguous typed parameter names at one stack offset must not be rendered"
        );

        let canonical_slot = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![crate::VisibleBinding {
                    name: "arg6".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 64,
                        signedness: crate::Signedness::Signed,
                    }),
                    kind: VisibleBindingKind::Param,
                    stack_slot: Some(StackSlotKey {
                        base: ExternalStackBase::StackPointer,
                        offset: 8,
                    }),
                    param_index: Some(6),
                    source_reg: None,
                }],
                stack_slots: BTreeMap::from([(
                    StackSlotKey {
                        base: ExternalStackBase::StackPointer,
                        offset: 8,
                    },
                    crate::ExternalStackSlotSpec {
                        name: "arg_8h".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        role: ExternalStackSlotRole::StackArg,
                        param_index: Some(6),
                        param_name: Some("arg7".to_string()),
                        source_reg: None,
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::StackPointer,
            8,
        )]));
        let authorization = canonical_slot
            .authorized_stack_param_owner_render(object, 8)
            .expect("canonical stack slot name should authorize");
        assert_eq!(authorization.name, "arg7");

        let param_home = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(FunctionSignatureSpec {
                    ret_type: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: crate::Signedness::Signed,
                    }),
                    params: vec![FunctionParamSpec {
                        name: "node".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                            "Node".to_string(),
                        )))),
                    }],
                }),
                stack_slots: BTreeMap::from([(
                    StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: -8,
                    },
                    crate::ExternalStackSlotSpec {
                        name: "node_home".to_string(),
                        ty: None,
                        role: ExternalStackSlotRole::ParamHome,
                        param_index: Some(0),
                        param_name: Some("node".to_string()),
                        source_reg: Some("rdi".to_string()),
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::FramePointer,
            -8,
        )]));
        let authorization = param_home
            .authorized_stack_param_owner_render(object, -8)
            .expect("typed parameter home should authorize original parameter owner");
        assert_eq!(authorization.name, "node");

        let stale_named_param_home = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(FunctionSignatureSpec {
                    ret_type: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: crate::Signedness::Signed,
                    }),
                    params: vec![
                        FunctionParamSpec {
                            name: "arg0".to_string(),
                            ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                                bits: 32,
                                signedness: crate::Signedness::Signed,
                            }))),
                        },
                        FunctionParamSpec {
                            name: "arg1".to_string(),
                            ty: Some(CTypeLike::Int {
                                bits: 32,
                                signedness: crate::Signedness::Signed,
                            }),
                        },
                    ],
                }),
                stack_slots: BTreeMap::from([(
                    StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: -8,
                    },
                    crate::ExternalStackSlotSpec {
                        name: "arg1_home".to_string(),
                        ty: None,
                        role: ExternalStackSlotRole::ParamHome,
                        param_index: Some(0),
                        param_name: Some("arg1".to_string()),
                        source_reg: Some("rdi".to_string()),
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            object,
            r2ssa::StackAddressBase::FramePointer,
            -8,
        )]));
        let authorization = stale_named_param_home
            .authorized_stack_param_owner_render(object, -8)
            .expect("parameter index should override a stale host-generated name");
        assert_eq!(authorization.name, "arg0");
        let raw_offset_param_home = param_home
            .clone()
            .with_render(test_render_with_stack_slots([(
                object,
                r2ssa::StackAddressBase::FramePointer,
                8,
            )]));
        assert!(
            raw_offset_param_home
                .authorized_stack_param_owner_render(object, 8)
                .is_none(),
            "frame-pointer parameter homes must match the canonical rendered offset, not the raw slot sign"
        );
        assert!(
            param_home
                .authorized_stack_slot_owner_render(object, -8, "node_home")
                .is_none(),
            "hidden parameter-home storage name must not become a rendered owner"
        );
    }

    #[test]
    fn stack_owner_render_by_offset_rejects_ambiguous_or_untyped_slots() {
        let typed_slot = (
            StackSlotKey {
                base: ExternalStackBase::StackPointer,
                offset: -8,
            },
            crate::ExternalStackSlotSpec {
                name: "local_buf".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: crate::Signedness::Signed,
                }),
                role: ExternalStackSlotRole::Local,
                ..crate::ExternalStackSlotSpec::default()
            },
        );
        let ambiguous = FunctionFacts::new(
            FunctionTypeFacts {
                stack_slots: BTreeMap::from([typed_slot.clone()]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([
            (
                r2ssa::ObjectId(1),
                r2ssa::StackAddressBase::StackPointer,
                -8,
            ),
            (
                r2ssa::ObjectId(2),
                r2ssa::StackAddressBase::StackPointer,
                -8,
            ),
        ]));
        assert!(
            ambiguous
                .authorized_stack_slot_owner_render_by_offset(-8, "local_buf")
                .is_none(),
            "offset-only bridge must refuse duplicate render objects"
        );

        let unknown_role = FunctionFacts::new(
            FunctionTypeFacts {
                stack_slots: BTreeMap::from([(
                    typed_slot.0,
                    crate::ExternalStackSlotSpec {
                        role: ExternalStackSlotRole::Unknown,
                        ..typed_slot.1.clone()
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            r2ssa::ObjectId(3),
            r2ssa::StackAddressBase::StackPointer,
            -8,
        )]));
        assert!(
            unknown_role
                .authorized_stack_slot_owner_render_by_offset(-8, "local_buf")
                .is_none(),
            "unknown stack-slot roles are not enough for certified owner rendering"
        );

        let untyped = FunctionFacts::new(
            FunctionTypeFacts {
                stack_slots: BTreeMap::from([(
                    typed_slot.0,
                    crate::ExternalStackSlotSpec {
                        ty: Some(CTypeLike::Unknown),
                        ..typed_slot.1
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(test_render_with_stack_slots([(
            r2ssa::ObjectId(4),
            r2ssa::StackAddressBase::StackPointer,
            -8,
        )]));
        assert!(
            untyped
                .authorized_stack_slot_owner_render_by_offset(-8, "local_buf")
                .is_none(),
            "unknown types are not enough for certified owner rendering"
        );
    }

    #[test]
    fn decompile_type_override_requires_render_authorized_signature() {
        let base_signature = crate::FunctionSignatureSpec {
            ret_type: Some(crate::CTypeLike::Void),
            params: Vec::new(),
        };
        let override_signature = crate::FunctionSignatureSpec {
            ret_type: Some(crate::CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Unsigned,
            }),
            params: vec![crate::FunctionParamSpec {
                name: "buf".to_string(),
                ty: Some(crate::CTypeLike::Pointer(Box::new(crate::CTypeLike::Int {
                    bits: 8,
                    signedness: crate::Signedness::Unsigned,
                }))),
            }],
        };
        let mut facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(base_signature.clone()),
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &base_signature,
                    [crate::SignatureCertificateSource::ExternalContext],
                ),
                ..FunctionTypeFacts::default()
            },
            None,
        );

        assert!(!facts.apply_decompile_type_override(FunctionTypeFacts {
            merged_signature: Some(override_signature.clone()),
            signature_certificate: None,
            ..FunctionTypeFacts::default()
        }));
        assert_eq!(
            facts.types.render_authorized_signature(),
            Some(&base_signature)
        );

        assert!(facts.apply_decompile_type_override(FunctionTypeFacts {
            merged_signature: Some(override_signature.clone()),
            signature_certificate: crate::SignatureCertificate::from_signature(
                &override_signature,
                [crate::SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        }));
        assert_eq!(
            facts.types.render_authorized_signature(),
            Some(&override_signature)
        );
    }

    #[test]
    fn decompile_fallback_comment_requires_fallback_route() {
        let fallback = DecompileRouteFacts {
            kind: DecompileRouteKind::FallbackComment,
            reason: Some("typed refusal".to_string()),
            fallback_comment: Some("/* typed fallback */".to_string()),
            use_prepared_semantic_view: false,
        };
        let standard_with_comment = DecompileRouteFacts {
            kind: DecompileRouteKind::Standard,
            reason: Some("must not render".to_string()),
            fallback_comment: Some("/* wrong route */".to_string()),
            use_prepared_semantic_view: false,
        };

        assert_eq!(
            FunctionFacts::default()
                .with_decompile_route(fallback)
                .decompile_fallback_comment(),
            Some("/* typed fallback */")
        );
        assert_eq!(
            FunctionFacts::default()
                .with_decompile_route(standard_with_comment)
                .decompile_fallback_comment(),
            None,
            "fallback comments are refusal payloads, not a side channel on executable routes"
        );
    }

    fn summary_with_effects(id: r2ssa::InterprocFunctionId) -> r2ssa::FunctionSemanticSummary {
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(id, Some("sym.effect".into()));
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                escape: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        summary.arg_effects.insert(
            1,
            r2ssa::SummaryArgEffect {
                write: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Write,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 2 },
                range: None,
            },
        });
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Escape,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 5 },
                range: None,
            },
        });
        summary.transfer_effects.push(r2ssa::SummaryTransferEffect {
            dst: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 3 },
                range: None,
            },
            src: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 4 },
                range: None,
            },
            len: r2ssa::SummaryTransferLength::Unknown,
        });
        summary
    }

    #[test]
    fn summary_rollup_out_params_require_writeback_evidence() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let helper = r2ssa::InterprocFunctionId(0x402000);
        let set = r2ssa::InterprocSummarySet {
            schema_version: r2ssa::interproc::INTERPROC_SUMMARY_SCHEMA_VERSION,
            root: Some(root),
            summaries: BTreeMap::from([
                (root, summary_with_effects(root)),
                (helper, summary_with_effects(helper)),
            ]),
            diagnostics: Default::default(),
        };

        let view = InterprocSummaryView::new(Some(set)).expect("current interproc report schema");

        assert_eq!(view.out_param_indices(), vec![1, 2, 3]);
        assert_eq!(
            view.rollup
                .as_ref()
                .expect("rollup")
                .out_param_facts
                .iter()
                .map(|fact| (&fact.evidence, &fact.source))
                .collect::<Vec<_>>(),
            vec![
                (
                    &OutParamCertificateEvidence::InterprocArgWrite,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocArgWrite,
                        param_index: 1,
                        effect_index: 1,
                    },
                ),
                (
                    &OutParamCertificateEvidence::InterprocMemoryWrite,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                        param_index: 2,
                        effect_index: 0,
                    },
                ),
                (
                    &OutParamCertificateEvidence::InterprocTransferDst,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocTransferDst,
                        param_index: 3,
                        effect_index: 0,
                    },
                ),
            ]
        );
        assert_eq!(view.pointer_param_indices(), &[0, 1, 2, 3, 4, 5]);
        let helper_view = view
            .helper_view_for_name("sym.effect")
            .expect("helper view");
        assert_eq!(
            out_param_indices_from_facts(&helper_view.out_param_facts),
            vec![1, 2, 3]
        );
        assert_eq!(helper_view.pointer_param_indices, vec![0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn interproc_summary_view_rejects_stale_or_mislabeled_reports() {
        let id = r2ssa::InterprocFunctionId(0x401000);
        let stale = r2ssa::InterprocSummarySet {
            schema_version: 1,
            ..r2ssa::InterprocSummarySet::default()
        };
        assert_eq!(
            InterprocSummaryView::new(Some(stale)),
            Err(r2ssa::interproc::InterprocSummarySchemaError::ReportSchemaVersion { found: 1 })
        );

        let summary_id = r2ssa::InterprocFunctionId(0x402000);
        let mut mislabeled = r2ssa::InterprocSummarySet::default();
        mislabeled.summaries.insert(
            id,
            r2ssa::FunctionSemanticSummary::unknown(summary_id, None),
        );
        assert_eq!(
            InterprocSummaryView::new(Some(mislabeled)),
            Err(
                r2ssa::interproc::InterprocSummarySchemaError::FunctionIdentityMismatch {
                    key: id,
                    summary_id,
                }
            )
        );
    }
}
