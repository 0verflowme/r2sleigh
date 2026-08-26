//! Pure declaration-placement and reaching-definition analysis.
//!
//! The sealed structured-region tree owns lexical ancestry. The canonical SSA
//! function owns CFG predecessors and dominance. This module joins those facts
//! with the read and write occurrences that survived final AST rewriting, then
//! returns an ephemeral decision. It deliberately retains neither a placement
//! table nor a dominance proof beside the tree that produced the answer.
//!
//! The region walk and occurrence grouping are linear. Must-assignment is a
//! forward bitset analysis over a sorted worklist, with cost
//! `O((bindings / word_bits) * (blocks + edges))` per fixpoint sweep.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{
    BinaryOp, CExpr, CFunction, CStmt, RenderObservationId, RenderObservationNode,
    inspect_render_observations,
};
use crate::binding_plan::{
    BindingId, BindingNameResolution, PlacementRead, PlacementRefusal, ValueDisposition,
};
use crate::structured_region::{RegionId, SealedStructuredRegionArtifact};
use r2ssa::{InstId, SSAFunction, UseSite};

/// Final render-order position of an occurrence after every AST rewrite.
///
/// The final marker walk assigns this monotonically. Equal positions are
/// permitted for one expression: reads are evaluated before its write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FinalOccurrenceOrder(pub(crate) u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FinalObservationScope {
    Exact {
        region: RegionId,
        order: FinalOccurrenceOrder,
    },
    Ambiguous,
}

/// One binding read that survived all AST rewriting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FinalBindingRead {
    pub(crate) binding: BindingId,
    pub(crate) source: PlacementRead,
    pub(crate) region: RegionId,
    pub(crate) block: u64,
    pub(crate) order: FinalOccurrenceOrder,
}

/// One binding write that survived all AST rewriting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FinalBindingWrite {
    pub(crate) binding: BindingId,
    pub(crate) inst: InstId,
    pub(crate) region: RegionId,
    pub(crate) block: u64,
    pub(crate) order: FinalOccurrenceOrder,
    /// Exact surviving marker that owns this write occurrence.
    pub(crate) observation: RenderObservationId,
    /// Whether this exact occurrence is a statement assignment that C permits
    /// the final emitter to replace with a declaration initializer.
    pub(crate) inline_eligible: bool,
}

/// Placement-relevant projection of the observation journal's private target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementObservationTarget {
    Use(UseSite),
    CertifiedValueRead {
        value: r2ssa::ValueId,
        at: InstId,
        binding: BindingId,
        symbol: crate::symbol::SymbolId,
    },
    Write(InstId),
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FinalPlacementOccurrences {
    reads: Box<[FinalBindingRead]>,
    writes: Box<[FinalBindingWrite]>,
}

impl FinalPlacementOccurrences {
    pub(crate) fn reads(&self) -> &[FinalBindingRead] {
        &self.reads
    }

    pub(crate) fn writes(&self) -> &[FinalBindingWrite] {
        &self.writes
    }
}

/// Join the final marker-bearing AST to the canonical source graph and sealed
/// binding plan. This is intentionally a one-shot emit-time calculation.
pub(crate) fn collect_final_placement_occurrences(
    function: &CFunction,
    regions: &SealedStructuredRegionArtifact,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    expected_observations: usize,
    mut target_for: impl FnMut(RenderObservationId) -> Option<PlacementObservationTarget>,
) -> Result<FinalPlacementOccurrences, PlacementAnalysisError> {
    crate::structured_region::validate_final_region_marker_tree(&function.body, regions)
        .map_err(PlacementAnalysisError::RegionMarkers)?;
    let mut targets = vec![None; expected_observations];
    let mut statement_assignment = vec![None; expected_observations];
    inspect_render_observations(function, expected_observations, |id, node| {
        let target = target_for(id)
            .ok_or(PlacementAnalysisError::MissingObservationTarget { observation: id })?;
        if let PlacementObservationTarget::CertifiedValueRead {
            value,
            at,
            binding,
            symbol,
        } = target
        {
            if !certified_value_read_matches(source, names, value, at, binding, symbol) {
                return Err(PlacementAnalysisError::InvalidCertifiedValueRead { value, at });
            }
            let RenderObservationNode::Expr(expr) = node else {
                return Err(PlacementAnalysisError::UnobservedBindingRead { binding });
            };
            if !expr_reads_symbol(expr, symbol) {
                return Err(PlacementAnalysisError::UnobservedBindingRead { binding });
            }
        }
        let index = id.index() as usize;
        targets[index] = Some(target);
        statement_assignment[index] = match node {
            RenderObservationNode::Stmt(stmt) => assigned_symbol(stmt),
            RenderObservationNode::Expr(_) => None,
        };
        Ok(())
    })
    .map_err(|error| match error {
        crate::ast::RenderObservationInspectError::Markers(error) => {
            PlacementAnalysisError::ObservationMarkers(error)
        }
        crate::ast::RenderObservationInspectError::Observer(error) => error,
    })?;

    let scoped = collect_final_observation_scopes(&function.body, regions, expected_observations);

    for (index, target) in targets.iter().copied().enumerate() {
        if matches!(
            target,
            Some(
                PlacementObservationTarget::Use(_)
                    | PlacementObservationTarget::CertifiedValueRead { .. }
                    | PlacementObservationTarget::Write(_)
            )
        ) {
            match scoped[index] {
                None => {
                    return Err(PlacementAnalysisError::UnscopedObservation {
                        observation: RenderObservationId::from_dense_index(index),
                    });
                }
                Some(FinalObservationScope::Ambiguous) => {
                    return Err(PlacementAnalysisError::AmbiguousExecutionOrder {
                        observation: RenderObservationId::from_dense_index(index),
                    });
                }
                Some(FinalObservationScope::Exact { .. }) => {}
            }
        }
    }

    let graph = source.graph();
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    for (index, target) in targets.iter().copied().enumerate() {
        let Some(FinalObservationScope::Exact { region, order }) = scoped[index] else {
            continue;
        };
        let observation = RenderObservationId::from_dense_index(index);
        match target.expect("only reachable observations receive a scope") {
            PlacementObservationTarget::Use(site) => {
                let inst = graph
                    .inst(site.inst)
                    .ok_or(PlacementAnalysisError::InvalidUse { site })?;
                let value = *inst
                    .inputs
                    .get(site.input_idx)
                    .ok_or(PlacementAnalysisError::InvalidUse { site })?;
                if let Some(binding) = bound_value(names, value)? {
                    let block = graph
                        .block(inst.block)
                        .ok_or(PlacementAnalysisError::InvalidUse { site })?
                        .addr;
                    reads.push(FinalBindingRead {
                        binding,
                        source: PlacementRead::Use(site),
                        region,
                        block,
                        order,
                    });
                }
            }
            PlacementObservationTarget::CertifiedValueRead {
                value,
                at,
                binding,
                symbol: _,
            } => {
                let inst = graph
                    .inst(at)
                    .ok_or(PlacementAnalysisError::InvalidWrite { inst: at })?;
                if bound_value(names, value)? == Some(binding) {
                    let block = graph
                        .block(inst.block)
                        .ok_or(PlacementAnalysisError::InvalidWrite { inst: at })?
                        .addr;
                    reads.push(FinalBindingRead {
                        binding,
                        source: PlacementRead::CertifiedValue { value, at },
                        region,
                        block,
                        order,
                    });
                }
            }
            PlacementObservationTarget::Write(inst_id) => {
                let inst = graph
                    .inst(inst_id)
                    .ok_or(PlacementAnalysisError::InvalidWrite { inst: inst_id })?;
                let value = inst
                    .output
                    .ok_or(PlacementAnalysisError::InvalidWrite { inst: inst_id })?;
                if let Some(binding) = bound_value(names, value)? {
                    let block = graph
                        .block(inst.block)
                        .ok_or(PlacementAnalysisError::InvalidWrite { inst: inst_id })?
                        .addr;
                    writes.push(FinalBindingWrite {
                        binding,
                        inst: inst_id,
                        region,
                        block,
                        order,
                        observation,
                        inline_eligible: statement_assignment[index]
                            == names.symbol_for_binding(binding),
                    });
                }
            }
            PlacementObservationTarget::Other => {}
        }
    }

    audit_plan_symbols(function, source, names, &targets)?;
    reads.sort_by_key(|read| (read.order, read.binding, read.source));
    writes.sort_by_key(|write| (write.order, write.binding, write.inst));
    Ok(FinalPlacementOccurrences {
        reads: reads.into_boxed_slice(),
        writes: writes.into_boxed_slice(),
    })
}

fn bound_value(
    names: &BindingNameResolution,
    value: r2ssa::ValueId,
) -> Result<Option<BindingId>, PlacementAnalysisError> {
    match names.disposition_for_value(value) {
        Some(ValueDisposition::Bound { binding }) => Ok(Some(*binding)),
        Some(ValueDisposition::Inline { .. } | ValueDisposition::Elided { .. }) => Ok(None),
        Some(ValueDisposition::Refused { .. }) => {
            Err(PlacementAnalysisError::RefusedPlannedValue { value })
        }
        None => Err(PlacementAnalysisError::MissingPlannedValue { value }),
    }
}

fn assigned_symbol(statement: &CStmt) -> Option<crate::symbol::SymbolId> {
    let CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        ..
    }) = statement.unobserved()
    else {
        return None;
    };
    match left.unobserved() {
        CExpr::Var(symbol) => Some(*symbol),
        _ => None,
    }
}

fn collect_final_observation_scopes(
    statements: &[CStmt],
    regions: &SealedStructuredRegionArtifact,
    expected_observations: usize,
) -> Vec<Option<FinalObservationScope>> {
    let mut scoped = vec![None; expected_observations];
    let mut order = 0_u64;
    for statement in statements {
        collect_stmt_observation_scopes(statement, None, regions, &mut order, &mut scoped);
    }
    scoped
}

fn record_observation_group(
    ids: &[RenderObservationId],
    region: Option<RegionId>,
    ambiguous: bool,
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    let current = FinalOccurrenceOrder(*order);
    *order = order.saturating_add(1);
    let Some(region) = region else { return };
    for id in ids {
        scoped[id.index() as usize] = Some(if ambiguous {
            FinalObservationScope::Ambiguous
        } else {
            FinalObservationScope::Exact {
                region,
                order: current,
            }
        });
    }
}

fn collect_expr_observation_ids(expr: &CExpr) -> Vec<RenderObservationId> {
    let mut ids = Vec::new();
    visit_expr_observations(expr, &mut |id| ids.push(id));
    ids
}

fn record_exact_expr_group(
    expr: &CExpr,
    leading: &mut Vec<RenderObservationId>,
    current: Option<RegionId>,
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    let mut ids = std::mem::take(leading);
    ids.extend(collect_expr_observation_ids(expr));
    record_observation_group(&ids, current, false, order, scoped);
}

fn collect_stmt_observation_scopes(
    statement: &CStmt,
    current: Option<RegionId>,
    regions: &SealedStructuredRegionArtifact,
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    if let CStmt::StructuredRegion { marker, stmt } = statement {
        let (region, _) = regions
            .node_for_marker(marker)
            .expect("the final marker tree was validated before scope collection");
        collect_stmt_observation_scopes(stmt, Some(region), regions, order, scoped);
        return;
    }
    let mut leading = Vec::new();
    let mut semantic = statement;
    while let CStmt::Observed { id, stmt } = semantic {
        leading.push(*id);
        semantic = stmt;
    }
    match semantic {
        CStmt::StructuredRegion { .. } => {
            record_observation_group(&leading, current, true, order, scoped);
            collect_stmt_observation_scopes(semantic, current, regions, order, scoped);
        }
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            record_exact_expr_group(expr, &mut leading, current, order, scoped);
        }
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                record_exact_expr_group(init, &mut leading, current, order, scoped);
            } else {
                record_observation_group(&leading, current, false, order, scoped);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            record_exact_expr_group(cond, &mut leading, current, order, scoped);
            collect_stmt_observation_scopes(then_body, current, regions, order, scoped);
            if let Some(else_body) = else_body {
                collect_stmt_observation_scopes(else_body, current, regions, order, scoped);
            }
        }
        CStmt::While { cond, body } => {
            record_exact_expr_group(cond, &mut leading, current, order, scoped);
            collect_stmt_observation_scopes(body, current, regions, order, scoped);
        }
        CStmt::DoWhile { body, cond } => {
            record_observation_group(&leading, current, true, order, scoped);
            collect_stmt_observation_scopes(body, current, regions, order, scoped);
            let ids = collect_expr_observation_ids(cond);
            record_observation_group(&ids, current, false, order, scoped);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            record_observation_group(&leading, current, true, order, scoped);
            if let Some(init) = init {
                collect_stmt_observation_scopes(init, current, regions, order, scoped);
            }
            if let Some(cond) = cond {
                let ids = collect_expr_observation_ids(cond);
                record_observation_group(&ids, current, false, order, scoped);
            }
            collect_stmt_observation_scopes(body, current, regions, order, scoped);
            if let Some(update) = update {
                let ids = collect_expr_observation_ids(update);
                record_observation_group(&ids, current, false, order, scoped);
            }
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            record_exact_expr_group(expr, &mut leading, current, order, scoped);
            for case in cases {
                let ids = collect_expr_observation_ids(&case.value);
                record_observation_group(&ids, current, true, order, scoped);
                for statement in &case.body {
                    collect_stmt_observation_scopes(statement, current, regions, order, scoped);
                }
            }
            if let Some(default) = default {
                for statement in default {
                    collect_stmt_observation_scopes(statement, current, regions, order, scoped);
                }
            }
        }
        CStmt::Block(statements) => {
            record_observation_group(&leading, current, true, order, scoped);
            for statement in statements {
                collect_stmt_observation_scopes(statement, current, regions, order, scoped);
            }
        }
        CStmt::Observed { .. } => unreachable!("leading observations were consumed"),
        CStmt::Empty
        | CStmt::Return(None)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {
            record_observation_group(&leading, current, false, order, scoped);
        }
    }
}

fn visit_expr_observations(expr: &CExpr, visit: &mut impl FnMut(RenderObservationId)) {
    if let CExpr::Observed { id, expr } = expr {
        visit(*id);
        visit_expr_observations(expr, visit);
        return;
    }
    match expr {
        CExpr::Observed { .. } => unreachable!("leading observation was consumed"),
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => visit_expr_observations(operand, visit),
        CExpr::Binary { left, right, .. } => {
            visit_expr_observations(left, visit);
            visit_expr_observations(right, visit);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            visit_expr_observations(cond, visit);
            visit_expr_observations(then_expr, visit);
            visit_expr_observations(else_expr, visit);
        }
        CExpr::Call { func, args, .. } => {
            visit_expr_observations(func, visit);
            for arg in args {
                visit_expr_observations(arg, visit);
            }
        }
        CExpr::Subscript { base, index } => {
            visit_expr_observations(base, visit);
            visit_expr_observations(index, visit);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            visit_expr_observations(base, visit);
        }
        CExpr::Comma(items) => {
            for item in items {
                visit_expr_observations(item, visit);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolAccess {
    Read,
    Write,
}

fn audit_plan_symbols(
    function: &CFunction,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    targets: &[Option<PlacementObservationTarget>],
) -> Result<(), PlacementAnalysisError> {
    let by_symbol = names
        .plan()
        .bindings()
        .filter_map(|(binding, _)| {
            names
                .symbol_for_binding(binding)
                .map(|symbol| (symbol, binding))
        })
        .collect::<BTreeMap<_, _>>();
    for local in &function.locals {
        if !by_symbol.contains_key(&local.name) {
            return Err(PlacementAnalysisError::UnauthorizedProgramVariable { symbol: local.name });
        }
    }
    for statement in &function.body {
        audit_statement(statement, source, names, targets, &by_symbol)?;
    }
    Ok(())
}

fn audit_statement(
    statement: &CStmt,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    targets: &[Option<PlacementObservationTarget>],
    by_symbol: &BTreeMap<crate::symbol::SymbolId, BindingId>,
) -> Result<(), PlacementAnalysisError> {
    if let CStmt::StructuredRegion { stmt, .. } = statement {
        return audit_statement(stmt, source, names, targets, by_symbol);
    }
    let mut active = Vec::new();
    let mut semantic = statement;
    while let CStmt::Observed { id, stmt } = semantic {
        if let Some(target) = targets.get(id.index() as usize).copied().flatten() {
            active.push(target);
        }
        semantic = stmt;
    }
    match semantic {
        CStmt::StructuredRegion { stmt, .. } => {
            audit_statement(stmt, source, names, targets, by_symbol)?;
        }
        CStmt::Observed { .. } => unreachable!("leading observations were consumed"),
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            audit_expr(
                expr,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CStmt::Decl { name, init, .. } => {
            audit_program_symbol(
                *name,
                SymbolAccess::Write,
                &active,
                source,
                names,
                by_symbol,
            )?;
            if let Some(init) = init {
                audit_expr(
                    init,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CStmt::Block(statements) => {
            for statement in statements {
                audit_statement(statement, source, names, targets, by_symbol)?;
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            audit_expr(
                cond,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            audit_statement(then_body, source, names, targets, by_symbol)?;
            if let Some(else_body) = else_body {
                audit_statement(else_body, source, names, targets, by_symbol)?;
            }
        }
        CStmt::While { cond, body } => {
            audit_expr(
                cond,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            audit_statement(body, source, names, targets, by_symbol)?;
        }
        CStmt::DoWhile { body, cond } => {
            audit_statement(body, source, names, targets, by_symbol)?;
            audit_expr(
                cond,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                audit_statement(init, source, names, targets, by_symbol)?;
            }
            if let Some(cond) = cond {
                audit_expr(
                    cond,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
            if let Some(update) = update {
                audit_expr(
                    update,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
            audit_statement(body, source, names, targets, by_symbol)?;
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            audit_expr(
                expr,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            for case in cases {
                audit_expr(
                    &case.value,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
                for statement in &case.body {
                    audit_statement(statement, source, names, targets, by_symbol)?;
                }
            }
            if let Some(default) = default {
                for statement in default {
                    audit_statement(statement, source, names, targets, by_symbol)?;
                }
            }
        }
        CStmt::Empty
        | CStmt::Return(None)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
    Ok(())
}

fn audit_expr(
    expr: &CExpr,
    access: SymbolAccess,
    active: &[PlacementObservationTarget],
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    targets: &[Option<PlacementObservationTarget>],
    by_symbol: &BTreeMap<crate::symbol::SymbolId, BindingId>,
) -> Result<(), PlacementAnalysisError> {
    if let CExpr::Observed { id, expr } = expr {
        let mut nested = active.to_vec();
        if let Some(target) = targets.get(id.index() as usize).copied().flatten() {
            nested.push(target);
        }
        return audit_expr(expr, access, &nested, source, names, targets, by_symbol);
    }
    match expr {
        CExpr::Var(symbol) => {
            audit_program_symbol(*symbol, access, active, source, names, by_symbol)?;
        }
        CExpr::Observed { .. } => unreachable!("leading observation was consumed"),
        CExpr::Unary { op, operand } => {
            if matches!(
                op,
                crate::ast::UnaryOp::PreInc
                    | crate::ast::UnaryOp::PreDec
                    | crate::ast::UnaryOp::PostInc
                    | crate::ast::UnaryOp::PostDec
            ) && matches!(operand.unobserved(), CExpr::Var(_))
            {
                audit_expr(
                    operand,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
                audit_expr(
                    operand,
                    SymbolAccess::Write,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            } else {
                audit_expr(
                    operand,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Binary { op, left, right } => {
            let assignment = matches!(
                op,
                BinaryOp::Assign
                    | BinaryOp::AddAssign
                    | BinaryOp::SubAssign
                    | BinaryOp::MulAssign
                    | BinaryOp::DivAssign
                    | BinaryOp::ModAssign
                    | BinaryOp::BitAndAssign
                    | BinaryOp::BitOrAssign
                    | BinaryOp::BitXorAssign
                    | BinaryOp::ShlAssign
                    | BinaryOp::ShrAssign
            );
            if assignment && matches!(left.unobserved(), CExpr::Var(_)) {
                if *op != BinaryOp::Assign {
                    audit_expr(
                        left,
                        SymbolAccess::Read,
                        active,
                        source,
                        names,
                        targets,
                        by_symbol,
                    )?;
                }
                audit_expr(
                    left,
                    SymbolAccess::Write,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            } else {
                audit_expr(
                    left,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
            audit_expr(
                right,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            for expr in [cond.as_ref(), then_expr.as_ref(), else_expr.as_ref()] {
                audit_expr(
                    expr,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Cast { expr, .. }
        | CExpr::Sizeof(expr)
        | CExpr::AddrOf(expr)
        | CExpr::Deref(expr)
        | CExpr::Paren(expr) => {
            audit_expr(
                expr,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CExpr::Call { func, args, .. } => {
            audit_expr(
                func,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            for arg in args {
                audit_expr(
                    arg,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Subscript { base, index } => {
            for expr in [base.as_ref(), index.as_ref()] {
                audit_expr(
                    expr,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            audit_expr(
                base,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CExpr::Comma(items) => {
            for item in items {
                audit_expr(
                    item,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
    Ok(())
}

fn audit_program_symbol(
    symbol: crate::symbol::SymbolId,
    access: SymbolAccess,
    active: &[PlacementObservationTarget],
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    by_symbol: &BTreeMap<crate::symbol::SymbolId, BindingId>,
) -> Result<(), PlacementAnalysisError> {
    let binding = by_symbol
        .get(&symbol)
        .copied()
        .ok_or(PlacementAnalysisError::UnauthorizedProgramVariable { symbol })?;
    if active
        .iter()
        .copied()
        .any(|target| target_authorizes_binding(target, access, binding, source, names))
    {
        return Ok(());
    }
    Err(match access {
        SymbolAccess::Read => PlacementAnalysisError::UnobservedBindingRead { binding },
        SymbolAccess::Write => PlacementAnalysisError::UnobservedBindingWrite { binding },
    })
}

fn target_authorizes_binding(
    target: PlacementObservationTarget,
    access: SymbolAccess,
    binding: BindingId,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
) -> bool {
    let graph = source.graph();
    match (target, access) {
        (PlacementObservationTarget::Use(site), SymbolAccess::Read) => graph
            .inst(site.inst)
            .and_then(|inst| inst.inputs.get(site.input_idx))
            .and_then(|value| names.disposition_for_value(*value))
            .is_some_and(|disposition| {
                matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
            }),
        (
            PlacementObservationTarget::CertifiedValueRead {
                value,
                at,
                binding: certified_binding,
                symbol,
            },
            SymbolAccess::Read,
        ) => {
            certified_binding == binding
                && certified_value_read_matches(
                    source,
                    names,
                    value,
                    at,
                    certified_binding,
                    symbol,
                )
        }
        (PlacementObservationTarget::Write(inst), SymbolAccess::Write) => graph
            .inst(inst)
            .and_then(|inst| inst.output)
            .and_then(|value| names.disposition_for_value(value))
            .is_some_and(|disposition| {
                matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
            }),
        (PlacementObservationTarget::Write(inst), SymbolAccess::Read) => {
            matches!(
                names.write_disposition(inst),
                Some(r2ssa::MachineWriteDisposition::Exact(
                    r2ssa::MachineWriteProjection::Insert { .. }
                ))
            ) && graph
                .inst(inst)
                .and_then(|inst| inst.output)
                .and_then(|value| names.disposition_for_value(value))
                .is_some_and(|disposition| {
                    matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
                })
        }
        (PlacementObservationTarget::Use(_), SymbolAccess::Write)
        | (PlacementObservationTarget::CertifiedValueRead { .. }, SymbolAccess::Write)
        | (PlacementObservationTarget::Other, _) => false,
    }
}

/// Revalidate the complete source-to-render identity chain carried by a
/// certified value-read marker. The return certificate owns `(ValueId,
/// InstId)`; the sealed binding plan owns `ValueId -> BindingId`; and name
/// resolution owns `BindingId -> SymbolId`. No one of those links is a
/// substitute for the others.
fn certified_value_read_matches(
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    value: r2ssa::ValueId,
    at: InstId,
    binding: BindingId,
    symbol: crate::symbol::SymbolId,
) -> bool {
    let graph = source.graph();
    let Some(certificate) = source
        .certificates()
        .returns_by_inst
        .get(&at)
        .and_then(|index| source.certificates().returns.get(*index))
    else {
        return false;
    };
    certificate.at == at
        && certificate.value == value
        && graph.op_site_for_inst(at) == Some((certificate.block_addr, certificate.op_index))
        && graph.inst(at).is_some_and(|inst| {
            matches!(
                inst.payload,
                r2ssa::InstPayload::Op(r2ssa::SSAOp::Return { .. })
            )
        })
        && matches!(
            names.disposition_for_value(value),
            Some(ValueDisposition::Bound { binding: owner }) if *owner == binding
        )
        && names.symbol_for_binding(binding) == Some(symbol)
}

/// Whether evaluating this expression reads the exact program symbol.
///
/// This follows C read semantics closely enough to reject a forged marker on
/// `symbol = literal`, `&symbol`, or `sizeof(symbol)`, while retaining exact
/// casts and slice projections produced from the planned value expression.
pub(crate) fn expr_reads_symbol(expr: &CExpr, symbol: crate::symbol::SymbolId) -> bool {
    match expr.unobserved() {
        CExpr::Var(actual) => *actual == symbol,
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => expr_reads_symbol(operand, symbol),
        CExpr::Binary { op, left, right } => {
            expr_reads_symbol(right, symbol)
                || (!matches!(op, BinaryOp::Assign) || !matches!(left.unobserved(), CExpr::Var(_)))
                    && expr_reads_symbol(left, symbol)
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_reads_symbol(cond, symbol)
                || expr_reads_symbol(then_expr, symbol)
                || expr_reads_symbol(else_expr, symbol)
        }
        CExpr::Call { func, args, .. } => {
            expr_reads_symbol(func, symbol) || args.iter().any(|arg| expr_reads_symbol(arg, symbol))
        }
        CExpr::Subscript { base, index } => {
            expr_reads_symbol(base, symbol) || expr_reads_symbol(index, symbol)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            expr_reads_symbol(base, symbol)
        }
        CExpr::Comma(items) => items.iter().any(|item| expr_reads_symbol(item, symbol)),
        CExpr::Observed { .. } => unreachable!("unobserved expression returned a wrapper"),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::External { .. }
        | CExpr::Sizeof(_)
        | CExpr::SizeofType(_)
        | CExpr::AddrOf(_) => false,
    }
}

/// A decision consumed immediately by final emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementDecision {
    /// The binding is already declared by the function signature and is
    /// assigned on function entry by the calling convention.
    ExternallyDeclared,
    /// Declare at the start of the lowest valid lexical region, then assign at
    /// each surviving write occurrence.
    LexicalDeclaration { region: RegionId },
    /// Replace the sole dominating assignment with a declaration initializer.
    Inline { write: InstId },
    /// Honest C cannot be emitted for this binding.
    Refused(PlacementRefusal),
}

/// Dense result in ascending `BindingId` order.
///
/// `None` means that the binding has no surviving occurrence and needs no C
/// declaration. The vector is transient and is not retained by `BindingPlan`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlacementDecisions {
    decisions: Box<[Option<PlacementDecision>]>,
}

impl PlacementDecisions {
    #[cfg(test)]
    pub(crate) fn decision(&self, binding: BindingId) -> Option<PlacementDecision> {
        self.decisions.get(binding.index()).copied().flatten()
    }

    pub(crate) fn iter(
        &self,
    ) -> impl ExactSizeIterator<Item = (BindingId, Option<PlacementDecision>)> + '_ {
        self.decisions.iter().enumerate().map(|(index, decision)| {
            let binding = BindingId::from_dense_index(index)
                .expect("placement decision count fits BindingId");
            (binding, *decision)
        })
    }
}

/// Structural mismatch between final occurrences and their two authorities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PlacementAnalysisError {
    BindingOutsidePlan { binding: BindingId },
    RegionOutsideArtifact { region: RegionId },
    BlockOutsideFunction { block: u64 },
    RegionDoesNotDominateOccurrence { region: RegionId, block: u64 },
    ExternalBindingOutsidePlan { binding: BindingId },
    RegionMarkers(crate::structured_region::StructuredRegionFinalizationError),
    ObservationMarkers(crate::ast::RenderObservationStripError),
    MissingObservationTarget { observation: RenderObservationId },
    InvalidUse { site: UseSite },
    InvalidWrite { inst: InstId },
    InvalidCertifiedValueRead { value: r2ssa::ValueId, at: InstId },
    MissingPlannedValue { value: r2ssa::ValueId },
    RefusedPlannedValue { value: r2ssa::ValueId },
    UnscopedObservation { observation: RenderObservationId },
    AmbiguousExecutionOrder { observation: RenderObservationId },
    UnauthorizedProgramVariable { symbol: crate::symbol::SymbolId },
    UnobservedBindingRead { binding: BindingId },
    UnobservedBindingWrite { binding: BindingId },
}

/// Failure to apply a derived decision to the exact final marked tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementApplicationError {
    Refused(PlacementRefusal),
    MissingBinding { binding: BindingId },
    MissingBindingSymbol { binding: BindingId },
    ExternalBindingMissingParameter { binding: BindingId },
    MissingRegion { region: RegionId },
    DuplicateRegion { region: RegionId },
    MissingInlineWrite { inst: InstId },
    DuplicateInlineWrite { inst: InstId },
}

/// Apply a decision set transactionally to the exact marker-bearing function.
pub(crate) fn apply_placement_decisions(
    function: &mut CFunction,
    regions: &SealedStructuredRegionArtifact,
    names: &BindingNameResolution,
    decisions: &PlacementDecisions,
    writes: &[FinalBindingWrite],
) -> Result<(), PlacementApplicationError> {
    let mut candidate = function.clone();
    let mut declarations =
        BTreeMap::<RegionId, Vec<(BindingId, crate::ast::CType, crate::symbol::SymbolId)>>::new();
    let plan = names.plan();

    for (binding, decision) in decisions.iter() {
        let symbol = names
            .symbol_for_binding(binding)
            .ok_or(PlacementApplicationError::MissingBindingSymbol { binding })?;
        let binding_fact = plan
            .binding(binding)
            .ok_or(PlacementApplicationError::MissingBinding { binding })?;
        match decision {
            None => candidate.locals.retain(|local| local.name != symbol),
            Some(PlacementDecision::ExternallyDeclared) => {
                if !candidate.params.iter().any(|param| param.name == symbol) {
                    return Err(PlacementApplicationError::ExternalBindingMissingParameter {
                        binding,
                    });
                }
                candidate.locals.retain(|local| local.name != symbol);
            }
            Some(PlacementDecision::LexicalDeclaration { region }) => {
                candidate.locals.retain(|local| local.name != symbol);
                declarations.entry(region).or_default().push((
                    binding,
                    binding_fact.declaration_type().clone(),
                    symbol,
                ));
            }
            Some(PlacementDecision::Inline { write }) => {
                candidate.locals.retain(|local| local.name != symbol);
                let matching = writes
                    .iter()
                    .filter(|occurrence| occurrence.binding == binding && occurrence.inst == write)
                    .collect::<Vec<_>>();
                let [occurrence] = matching.as_slice() else {
                    return Err(if matching.is_empty() {
                        PlacementApplicationError::MissingInlineWrite { inst: write }
                    } else {
                        PlacementApplicationError::DuplicateInlineWrite { inst: write }
                    });
                };
                let replacements = inline_exact_write(
                    &mut candidate.body,
                    occurrence.observation,
                    symbol,
                    binding_fact.declaration_type(),
                );
                if replacements != 1 {
                    return Err(if replacements == 0 {
                        PlacementApplicationError::MissingInlineWrite { inst: write }
                    } else {
                        PlacementApplicationError::DuplicateInlineWrite { inst: write }
                    });
                }
            }
            Some(PlacementDecision::Refused(reason)) => {
                return Err(PlacementApplicationError::Refused(reason));
            }
        }
    }

    for (region, declarations) in &mut declarations {
        declarations.sort_by_key(|(binding, _, _)| *binding);
        let statements = declarations
            .iter()
            .map(|(_, ty, name)| CStmt::Decl {
                ty: ty.clone(),
                name: *name,
                init: None,
            })
            .collect::<Vec<_>>();
        match insert_region_declarations(&mut candidate.body, regions, *region, &statements) {
            0 => return Err(PlacementApplicationError::MissingRegion { region: *region }),
            1 => {}
            _ => return Err(PlacementApplicationError::DuplicateRegion { region: *region }),
        }
    }

    *function = candidate;
    Ok(())
}

fn insert_region_declarations(
    statements: &mut [CStmt],
    regions: &SealedStructuredRegionArtifact,
    target: RegionId,
    declarations: &[CStmt],
) -> usize {
    statements
        .iter_mut()
        .map(|statement| {
            insert_region_declarations_in_stmt(statement, regions, target, declarations)
        })
        .sum()
}

fn insert_region_declarations_in_stmt(
    statement: &mut CStmt,
    regions: &SealedStructuredRegionArtifact,
    target: RegionId,
    declarations: &[CStmt],
) -> usize {
    if let CStmt::StructuredRegion { marker, stmt } = statement {
        let is_target = regions
            .node_for_marker(marker)
            .is_some_and(|(region, _)| region == target);
        if is_target {
            let semantic = std::mem::replace(stmt.as_mut(), CStmt::Empty);
            *stmt = Box::new(match semantic {
                CStmt::Block(mut statements) => {
                    let mut placed = declarations.to_vec();
                    placed.append(&mut statements);
                    CStmt::Block(placed)
                }
                semantic => {
                    let mut placed = declarations.to_vec();
                    placed.push(semantic);
                    CStmt::Block(placed)
                }
            });
            return 1;
        }
        return insert_region_declarations_in_stmt(stmt, regions, target, declarations);
    }

    if let CStmt::Observed { stmt, .. } = statement {
        return insert_region_declarations_in_stmt(stmt, regions, target, declarations);
    }

    match statement {
        CStmt::StructuredRegion { .. } | CStmt::Observed { .. } => {
            unreachable!("leading wrappers handled above")
        }
        CStmt::Block(statements) => {
            insert_region_declarations(statements, regions, target, declarations)
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            insert_region_declarations_in_stmt(then_body, regions, target, declarations)
                + else_body.as_deref_mut().map_or(0, |body| {
                    insert_region_declarations_in_stmt(body, regions, target, declarations)
                })
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            insert_region_declarations_in_stmt(body, regions, target, declarations)
        }
        CStmt::For { init, body, .. } => {
            init.as_deref_mut().map_or(0, |init| {
                insert_region_declarations_in_stmt(init, regions, target, declarations)
            }) + insert_region_declarations_in_stmt(body, regions, target, declarations)
        }
        CStmt::Switch { cases, default, .. } => {
            let cases = cases
                .iter_mut()
                .map(|case| {
                    insert_region_declarations(&mut case.body, regions, target, declarations)
                })
                .sum::<usize>();
            cases
                + default.as_mut().map_or(0, |body| {
                    insert_region_declarations(body, regions, target, declarations)
                })
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => 0,
    }
}

fn inline_exact_write(
    statements: &mut [CStmt],
    target: RenderObservationId,
    symbol: crate::symbol::SymbolId,
    ty: &crate::ast::CType,
) -> usize {
    statements
        .iter_mut()
        .map(|statement| inline_exact_write_in_stmt(statement, target, symbol, ty))
        .sum()
}

fn inline_exact_write_in_stmt(
    statement: &mut CStmt,
    target: RenderObservationId,
    symbol: crate::symbol::SymbolId,
    ty: &crate::ast::CType,
) -> usize {
    if let CStmt::Observed { id, stmt } = statement {
        if *id == target {
            return usize::from(replace_assignment_with_declaration(stmt, symbol, ty));
        }
        return inline_exact_write_in_stmt(stmt, target, symbol, ty);
    }
    match statement {
        CStmt::StructuredRegion { stmt, .. } => {
            inline_exact_write_in_stmt(stmt, target, symbol, ty)
        }
        CStmt::Block(statements) => inline_exact_write(statements, target, symbol, ty),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            inline_exact_write_in_stmt(then_body, target, symbol, ty)
                + else_body.as_deref_mut().map_or(0, |body| {
                    inline_exact_write_in_stmt(body, target, symbol, ty)
                })
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            inline_exact_write_in_stmt(body, target, symbol, ty)
        }
        CStmt::For { init, body, .. } => {
            init.as_deref_mut().map_or(0, |init| {
                inline_exact_write_in_stmt(init, target, symbol, ty)
            }) + inline_exact_write_in_stmt(body, target, symbol, ty)
        }
        CStmt::Switch { cases, default, .. } => {
            let cases = cases
                .iter_mut()
                .map(|case| inline_exact_write(&mut case.body, target, symbol, ty))
                .sum::<usize>();
            cases
                + default
                    .as_mut()
                    .map_or(0, |body| inline_exact_write(body, target, symbol, ty))
        }
        CStmt::Observed { .. } => unreachable!("leading observation handled above"),
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => 0,
    }
}

fn replace_assignment_with_declaration(
    statement: &mut CStmt,
    symbol: crate::symbol::SymbolId,
    ty: &crate::ast::CType,
) -> bool {
    if let CStmt::Observed { stmt, .. } = statement {
        return replace_assignment_with_declaration(stmt, symbol, ty);
    }
    let CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        ..
    }) = statement
    else {
        return false;
    };
    if !matches!(left.unobserved(), CExpr::Var(name) if *name == symbol) {
        return false;
    }
    let CStmt::Expr(CExpr::Binary { right, .. }) = std::mem::replace(statement, CStmt::Empty)
    else {
        unreachable!("assignment shape was checked before move")
    };
    *statement = CStmt::Decl {
        ty: ty.clone(),
        name: symbol,
        init: Some(*right),
    };
    true
}

/// Derive all declaration decisions from canonical facts and final occurrences.
pub(crate) fn derive_placement_decisions(
    regions: &SealedStructuredRegionArtifact,
    function: &SSAFunction,
    binding_count: usize,
    externally_declared: &BTreeSet<BindingId>,
    reads: &[FinalBindingRead],
    writes: &[FinalBindingWrite],
) -> Result<PlacementDecisions, PlacementAnalysisError> {
    derive_with_cfg(
        regions,
        function,
        binding_count,
        externally_declared,
        reads,
        writes,
    )
}

trait PlacementControlFlow {
    fn entry(&self) -> u64;
    fn block_addrs(&self) -> Vec<u64>;
    fn predecessors(&self, block: u64) -> Vec<u64>;
    fn successors(&self, block: u64) -> Vec<u64>;
    fn dominates(&self, dominator: u64, block: u64) -> bool;
}

impl PlacementControlFlow for SSAFunction {
    fn entry(&self) -> u64 {
        self.entry
    }

    fn block_addrs(&self) -> Vec<u64> {
        SSAFunction::block_addrs(self).to_vec()
    }

    fn predecessors(&self, block: u64) -> Vec<u64> {
        SSAFunction::predecessors(self, block)
    }

    fn successors(&self, block: u64) -> Vec<u64> {
        SSAFunction::successors(self, block)
    }

    fn dominates(&self, dominator: u64, block: u64) -> bool {
        SSAFunction::dominates(self, dominator, block)
    }
}

fn derive_with_cfg<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    binding_count: usize,
    externally_declared: &BTreeSet<BindingId>,
    reads: &[FinalBindingRead],
    writes: &[FinalBindingWrite],
) -> Result<PlacementDecisions, PlacementAnalysisError> {
    let mut block_addrs = cfg.block_addrs();
    block_addrs.sort_unstable();
    block_addrs.dedup();
    let block_indices = block_addrs
        .iter()
        .copied()
        .enumerate()
        .map(|(index, block)| (block, index))
        .collect::<BTreeMap<_, _>>();

    if let Some(binding) = externally_declared
        .iter()
        .copied()
        .find(|binding| binding.index() >= binding_count)
    {
        return Err(PlacementAnalysisError::ExternalBindingOutsidePlan { binding });
    }

    for read in reads {
        validate_occurrence(
            regions,
            cfg,
            binding_count,
            &block_indices,
            read.binding,
            read.region,
            read.block,
        )?;
    }
    for write in writes {
        validate_occurrence(
            regions,
            cfg,
            binding_count,
            &block_indices,
            write.binding,
            write.region,
            write.block,
        )?;
    }

    let mut occurrences = vec![Vec::<Occurrence>::new(); binding_count];
    for read in reads {
        occurrences[read.binding.index()].push(Occurrence {
            region: read.region,
            block: read.block,
            order: read.order,
            kind: OccurrenceKind::Read(read.source),
        });
    }
    for write in writes {
        occurrences[write.binding.index()].push(Occurrence {
            region: write.region,
            block: write.block,
            order: write.order,
            kind: OccurrenceKind::Write {
                inst: write.inst,
                inline_eligible: write.inline_eligible,
            },
        });
    }
    for binding_occurrences in &mut occurrences {
        binding_occurrences.sort_by_key(Occurrence::sort_key);
    }

    let must_in = must_assignment_inputs(
        cfg,
        binding_count,
        &block_addrs,
        &block_indices,
        &occurrences,
        externally_declared,
    );
    let mut decisions = vec![None; binding_count];

    for (binding_index, binding_occurrences) in occurrences.iter().enumerate() {
        if binding_occurrences.is_empty() {
            continue;
        }
        let binding = BindingId::from_dense_index(binding_index)
            .expect("binding_count is already addressable by BindingId occurrences");
        let writes_for_binding = binding_occurrences
            .iter()
            .filter_map(|occurrence| match occurrence.kind {
                OccurrenceKind::Write {
                    inst,
                    inline_eligible,
                } => Some((occurrence, inst, inline_eligible)),
                OccurrenceKind::Read(_) => None,
            })
            .collect::<Vec<_>>();
        if externally_declared.contains(&binding) {
            decisions[binding_index] = Some(PlacementDecision::ExternallyDeclared);
            continue;
        }
        if writes_for_binding.is_empty() {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::MissingDefinition { binding },
            ));
            continue;
        }

        if !occurrence_regions_have_proven_order(regions, binding_occurrences) {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::UnprovableExecutionOrder { binding },
            ));
            continue;
        }

        if let Some(read) =
            first_read_before_assignment(binding, binding_occurrences, &must_in, &block_indices)
        {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment { binding, read },
            ));
            continue;
        }

        let Some(region) = lowest_dominating_region(regions, cfg, binding_occurrences) else {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::NoDominatingRegion { binding },
            ));
            continue;
        };

        if let [(write, inst, inline_eligible)] = writes_for_binding.as_slice()
            && *inline_eligible
            && binding_occurrences.iter().all(|occurrence| {
                matches!(occurrence.kind, OccurrenceKind::Write { .. })
                    || (write.order <= occurrence.order
                        && cfg.dominates(write.block, occurrence.block))
            })
        {
            decisions[binding_index] = Some(PlacementDecision::Inline { write: *inst });
        } else {
            decisions[binding_index] = Some(PlacementDecision::LexicalDeclaration { region });
        }
    }

    Ok(PlacementDecisions {
        decisions: decisions.into_boxed_slice(),
    })
}

fn occurrence_regions_have_proven_order(
    regions: &SealedStructuredRegionArtifact,
    occurrences: &[Occurrence],
) -> bool {
    let mut by_block = BTreeMap::<u64, BTreeSet<RegionId>>::new();
    for occurrence in occurrences {
        by_block
            .entry(occurrence.block)
            .or_default()
            .insert(occurrence.region);
    }
    by_block.values().all(|block_regions| {
        block_regions.iter().all(|left| {
            block_regions.iter().all(|right| {
                region_is_ancestor(regions, *left, *right)
                    || region_is_ancestor(regions, *right, *left)
            })
        })
    })
}

fn region_is_ancestor(
    regions: &SealedStructuredRegionArtifact,
    ancestor: RegionId,
    mut region: RegionId,
) -> bool {
    loop {
        if region == ancestor {
            return true;
        }
        let Some(parent) = regions.node(region).and_then(|node| node.parent()) else {
            return false;
        };
        region = parent;
    }
}

fn validate_occurrence<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    binding_count: usize,
    block_indices: &BTreeMap<u64, usize>,
    binding: BindingId,
    region: RegionId,
    block: u64,
) -> Result<(), PlacementAnalysisError> {
    if binding.index() >= binding_count {
        return Err(PlacementAnalysisError::BindingOutsidePlan { binding });
    }
    let Some(node) = regions.node(region) else {
        return Err(PlacementAnalysisError::RegionOutsideArtifact { region });
    };
    if !block_indices.contains_key(&block) {
        return Err(PlacementAnalysisError::BlockOutsideFunction { block });
    }
    if !cfg.dominates(node.entry(), block) {
        return Err(PlacementAnalysisError::RegionDoesNotDominateOccurrence { region, block });
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Occurrence {
    region: RegionId,
    block: u64,
    order: FinalOccurrenceOrder,
    kind: OccurrenceKind,
}

impl Occurrence {
    fn sort_key(&self) -> (FinalOccurrenceOrder, u8, u64, usize, u32, usize) {
        match self.kind {
            OccurrenceKind::Read(PlacementRead::Use(site)) => (
                self.order,
                0,
                self.block,
                self.region.index(),
                site.inst.0,
                site.input_idx,
            ),
            OccurrenceKind::Read(PlacementRead::CertifiedValue { value, at }) => (
                self.order,
                0,
                self.block,
                self.region.index(),
                at.0,
                value.0 as usize,
            ),
            OccurrenceKind::Write { inst, .. } => {
                (self.order, 1, self.block, self.region.index(), inst.0, 0)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OccurrenceKind {
    Read(PlacementRead),
    Write { inst: InstId, inline_eligible: bool },
}

fn lowest_dominating_region<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    occurrences: &[Occurrence],
) -> Option<RegionId> {
    let mut candidate = occurrences.first()?.region;
    for occurrence in &occurrences[1..] {
        candidate = lowest_common_ancestor(regions, candidate, occurrence.region)?;
    }

    loop {
        let node = regions.node(candidate)?;
        if occurrences
            .iter()
            .all(|occurrence| cfg.dominates(node.entry(), occurrence.block))
        {
            return Some(candidate);
        }
        candidate = node.parent()?;
    }
}

fn lowest_common_ancestor(
    regions: &SealedStructuredRegionArtifact,
    mut left: RegionId,
    mut right: RegionId,
) -> Option<RegionId> {
    let mut left_depth = regions.node(left)?.depth();
    let mut right_depth = regions.node(right)?.depth();
    while left_depth > right_depth {
        left = regions.node(left)?.parent()?;
        left_depth -= 1;
    }
    while right_depth > left_depth {
        right = regions.node(right)?.parent()?;
        right_depth -= 1;
    }
    while left != right {
        left = regions.node(left)?.parent()?;
        right = regions.node(right)?.parent()?;
    }
    Some(left)
}

fn first_read_before_assignment(
    binding: BindingId,
    occurrences: &[Occurrence],
    must_in: &[DenseBindingSet],
    block_indices: &BTreeMap<u64, usize>,
) -> Option<PlacementRead> {
    let mut by_rendered_block = BTreeMap::<u64, Vec<&Occurrence>>::new();
    for occurrence in occurrences {
        by_rendered_block
            .entry(occurrence.block)
            .or_default()
            .push(occurrence);
    }

    for (block, mut block_occurrences) in by_rendered_block {
        block_occurrences.sort_by_key(|occurrence| occurrence.sort_key());
        let block_index = block_indices[&block];
        let mut assigned = must_in[block_index].contains(binding);
        for occurrence in block_occurrences {
            match occurrence.kind {
                OccurrenceKind::Read(read) if !assigned => return Some(read),
                OccurrenceKind::Read(_) => {}
                OccurrenceKind::Write { .. } => assigned = true,
            }
        }
    }
    None
}

fn must_assignment_inputs<C: PlacementControlFlow + ?Sized>(
    cfg: &C,
    binding_count: usize,
    block_addrs: &[u64],
    block_indices: &BTreeMap<u64, usize>,
    occurrences: &[Vec<Occurrence>],
    externally_declared: &BTreeSet<BindingId>,
) -> Vec<DenseBindingSet> {
    let mut generated = vec![DenseBindingSet::empty(binding_count); block_addrs.len()];
    for (binding_index, binding_occurrences) in occurrences.iter().enumerate() {
        let binding = BindingId::from_dense_index(binding_index)
            .expect("binding occurrence index fits BindingId");
        for occurrence in binding_occurrences {
            if matches!(occurrence.kind, OccurrenceKind::Write { .. }) {
                generated[block_indices[&occurrence.block]].insert(binding);
            }
        }
    }

    let mut inputs = vec![DenseBindingSet::all(binding_count); block_addrs.len()];
    let mut outputs = vec![DenseBindingSet::all(binding_count); block_addrs.len()];
    let mut worklist = (0..block_addrs.len()).collect::<BTreeSet<_>>();
    while let Some(block_index) = worklist.pop_first() {
        let block = block_addrs[block_index];
        let mut predecessors = cfg.predecessors(block);
        predecessors.sort_unstable();
        predecessors.dedup();
        let next_input = if block == cfg.entry() {
            DenseBindingSet::from_bindings(binding_count, externally_declared)
        } else if predecessors.is_empty() {
            DenseBindingSet::empty(binding_count)
        } else {
            let first = predecessors.remove(0);
            let mut intersection = outputs[block_indices[&first]].clone();
            for predecessor in predecessors {
                intersection.intersect_with(&outputs[block_indices[&predecessor]]);
            }
            intersection
        };
        let mut next_output = next_input.clone();
        next_output.union_with(&generated[block_index]);
        let output_changed = next_output != outputs[block_index];
        inputs[block_index] = next_input;
        outputs[block_index] = next_output;
        if output_changed {
            let mut successors = cfg.successors(block);
            successors.sort_unstable();
            successors.dedup();
            for successor in successors {
                worklist.insert(block_indices[&successor]);
            }
        }
    }
    inputs
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DenseBindingSet {
    words: Vec<u64>,
    binding_count: usize,
}

impl DenseBindingSet {
    fn empty(binding_count: usize) -> Self {
        Self {
            words: vec![0; binding_count.div_ceil(u64::BITS as usize)],
            binding_count,
        }
    }

    fn all(binding_count: usize) -> Self {
        let mut set = Self {
            words: vec![u64::MAX; binding_count.div_ceil(u64::BITS as usize)],
            binding_count,
        };
        if let Some(last) = set.words.last_mut() {
            let used = binding_count % u64::BITS as usize;
            if used != 0 {
                *last &= (1_u64 << used) - 1;
            }
        }
        set
    }

    fn from_bindings(binding_count: usize, bindings: &BTreeSet<BindingId>) -> Self {
        let mut set = Self::empty(binding_count);
        for binding in bindings {
            set.insert(*binding);
        }
        set
    }

    fn contains(&self, binding: BindingId) -> bool {
        let index = binding.index();
        index < self.binding_count
            && self.words[index / u64::BITS as usize] & (1_u64 << (index % u64::BITS as usize)) != 0
    }

    fn insert(&mut self, binding: BindingId) {
        let index = binding.index();
        debug_assert!(index < self.binding_count);
        self.words[index / u64::BITS as usize] |= 1_u64 << (index % u64::BITS as usize);
    }

    fn intersect_with(&mut self, other: &Self) {
        debug_assert_eq!(self.binding_count, other.binding_count);
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left &= *right;
        }
    }

    fn union_with(&mut self, other: &Self) {
        debug_assert_eq!(self.binding_count, other.binding_count);
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left |= *right;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::Region;
    use crate::structured_region::{
        StructuredRegionDraft, StructuredRegionKind, StructuredRegionMarker, seal_structured_body,
    };
    use crate::symbol::{SymbolRole, SymbolTable};

    fn observation(index: u32) -> RenderObservationId {
        crate::observation_journal::test_render_observation_id(index)
    }

    #[derive(Debug)]
    struct TestCfg {
        entry: u64,
        successors: BTreeMap<u64, Vec<u64>>,
        predecessors: BTreeMap<u64, Vec<u64>>,
        dominators: BTreeMap<u64, BTreeSet<u64>>,
    }

    impl TestCfg {
        fn new(entry: u64, edges: &[(u64, u64)]) -> Self {
            let mut blocks = BTreeSet::from([entry]);
            let mut successors = BTreeMap::<u64, Vec<u64>>::new();
            let mut predecessors = BTreeMap::<u64, Vec<u64>>::new();
            for &(from, to) in edges {
                blocks.extend([from, to]);
                successors.entry(from).or_default().push(to);
                predecessors.entry(to).or_default().push(from);
            }
            for block in &blocks {
                successors.entry(*block).or_default().sort_unstable();
                predecessors.entry(*block).or_default().sort_unstable();
            }

            let mut dominators = blocks
                .iter()
                .map(|block| {
                    let set = if *block == entry {
                        BTreeSet::from([entry])
                    } else {
                        blocks.clone()
                    };
                    (*block, set)
                })
                .collect::<BTreeMap<_, _>>();
            loop {
                let mut changed = false;
                for block in blocks.iter().copied().filter(|block| *block != entry) {
                    let preds = &predecessors[&block];
                    let mut next = if let Some(first) = preds.first() {
                        dominators[first].clone()
                    } else {
                        BTreeSet::new()
                    };
                    for predecessor in preds.iter().skip(1) {
                        next = next
                            .intersection(&dominators[predecessor])
                            .copied()
                            .collect();
                    }
                    next.insert(block);
                    if next != dominators[&block] {
                        dominators.insert(block, next);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            Self {
                entry,
                successors,
                predecessors,
                dominators,
            }
        }
    }

    impl PlacementControlFlow for TestCfg {
        fn entry(&self) -> u64 {
            self.entry
        }

        fn block_addrs(&self) -> Vec<u64> {
            self.successors.keys().copied().collect()
        }

        fn predecessors(&self, block: u64) -> Vec<u64> {
            self.predecessors[&block].clone()
        }

        fn successors(&self, block: u64) -> Vec<u64> {
            self.successors[&block].clone()
        }

        fn dominates(&self, dominator: u64, block: u64) -> bool {
            self.dominators[&block].contains(&dominator)
        }
    }

    fn diamond_regions() -> SealedStructuredRegionArtifact {
        let region = Region::Sequence(vec![
            Region::IfThenElse {
                cond_block: 0x1000,
                then_region: Box::new(Region::Block(0x1010)),
                else_region: Some(Box::new(Region::Block(0x1020))),
                merge_block: Some(0x1030),
            },
            Region::Block(0x1030),
        ]);
        StructuredRegionDraft::from_region(0x1000, &region)
            .expect("diamond region")
            .seal()
    }

    fn region_with_entry(
        regions: &SealedStructuredRegionArtifact,
        entry: u64,
        kind: StructuredRegionKind,
    ) -> RegionId {
        let index = regions
            .nodes()
            .iter()
            .position(|node| node.entry() == entry && node.kind() == kind)
            .expect("region entry");
        regions
            .node_for_anchor(
                regions.authority(),
                regions.nodes()[index].emission_anchor(),
            )
            .expect("dense region")
            .0
    }

    fn diamond_cfg() -> TestCfg {
        TestCfg::new(
            0x1000,
            &[
                (0x1000, 0x1010),
                (0x1000, 0x1020),
                (0x1010, 0x1030),
                (0x1020, 0x1030),
            ],
        )
    }

    #[test]
    fn diamond_with_both_arms_assigned_places_one_lexical_declaration() {
        let regions = diamond_regions();
        let cfg = diamond_cfg();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let then_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let else_region = region_with_entry(&regions, 0x1020, StructuredRegionKind::Block);
        let merge_region = region_with_entry(&regions, 0x1030, StructuredRegionKind::Block);
        let writes = [
            FinalBindingWrite {
                binding,
                inst: InstId(1),
                region: then_region,
                block: 0x1010,
                order: FinalOccurrenceOrder(1),
                observation: observation(1),
                inline_eligible: true,
            },
            FinalBindingWrite {
                binding,
                inst: InstId(2),
                region: else_region,
                block: 0x1020,
                order: FinalOccurrenceOrder(2),
                observation: observation(2),
                inline_eligible: true,
            },
        ];
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::Use(UseSite {
                inst: InstId(3),
                input_idx: 0,
            }),
            region: merge_region,
            block: 0x1030,
            order: FinalOccurrenceOrder(3),
        }];

        let decisions = derive_with_cfg(&regions, &cfg, 1, &BTreeSet::new(), &reads, &writes)
            .expect("placement");
        let sequence = regions.source_root();
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::LexicalDeclaration { region: sequence })
        );
    }

    #[test]
    fn diamond_with_one_arm_unassigned_refuses_merge_read() {
        let regions = diamond_regions();
        let cfg = diamond_cfg();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let then_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let merge_region = region_with_entry(&regions, 0x1030, StructuredRegionKind::Block);
        let site = UseSite {
            inst: InstId(3),
            input_idx: 0,
        };
        let writes = [FinalBindingWrite {
            binding,
            inst: InstId(1),
            region: then_region,
            block: 0x1010,
            order: FinalOccurrenceOrder(1),
            observation: observation(1),
            inline_eligible: true,
        }];
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::Use(site),
            region: merge_region,
            block: 0x1030,
            order: FinalOccurrenceOrder(2),
        }];

        let decisions = derive_with_cfg(&regions, &cfg, 1, &BTreeSet::new(), &reads, &writes)
            .expect("placement");
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment {
                    binding,
                    read: PlacementRead::Use(site),
                }
            ))
        );
    }

    #[test]
    fn one_dominating_write_is_inlined_at_its_exact_assignment() {
        let region = Region::Sequence(vec![Region::Block(0x1000), Region::Block(0x1010)]);
        let regions = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("linear region")
            .seal();
        let cfg = TestCfg::new(0x1000, &[(0x1000, 0x1010)]);
        let binding = BindingId::from_dense_index(0).expect("binding");
        let write_region = region_with_entry(&regions, 0x1000, StructuredRegionKind::Block);
        let read_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let write = InstId(1);
        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::new(),
            &[FinalBindingRead {
                binding,
                source: PlacementRead::Use(UseSite {
                    inst: InstId(2),
                    input_idx: 0,
                }),
                region: read_region,
                block: 0x1010,
                order: FinalOccurrenceOrder(2),
            }],
            &[FinalBindingWrite {
                binding,
                inst: write,
                region: write_region,
                block: 0x1000,
                order: FinalOccurrenceOrder(1),
                observation: observation(1),
                inline_eligible: true,
            }],
        )
        .expect("placement");

        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Inline { write })
        );
    }

    #[test]
    fn certified_parameter_read_uses_entry_assignment_without_a_local() {
        let region = Region::Block(0x1000);
        let regions = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("parameter region")
            .seal();
        let cfg = TestCfg::new(0x1000, &[]);
        let binding = BindingId::from_dense_index(0).expect("binding");
        let block_region = region_with_entry(&regions, 0x1000, StructuredRegionKind::Block);
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::Use(UseSite {
                inst: InstId(0),
                input_idx: 0,
            }),
            region: block_region,
            block: 0x1000,
            order: FinalOccurrenceOrder(0),
        }];

        let decisions = derive_with_cfg(&regions, &cfg, 1, &BTreeSet::from([binding]), &reads, &[])
            .expect("parameter placement");
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::ExternallyDeclared)
        );

        let uncertified = derive_with_cfg(&regions, &cfg, 1, &BTreeSet::new(), &reads, &[])
            .expect("uncertified placement");
        assert_eq!(
            uncertified.decision(binding),
            Some(PlacementDecision::Refused(
                PlacementRefusal::MissingDefinition { binding }
            ))
        );
    }

    #[test]
    fn exact_region_insertion_uses_the_sealed_anchor_not_the_block_address() {
        let repeated_entry = CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Block(vec![
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
                    CStmt::comment("first"),
                ),
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
                    CStmt::comment("second"),
                ),
            ]),
        );
        let sealed = seal_structured_body(repeated_entry).expect("sealed occurrences");
        let target = sealed
            .regions()
            .node_for_anchor(
                sealed.regions().authority(),
                sealed.regions().nodes()[2].emission_anchor(),
            )
            .expect("second occurrence")
            .0;
        let (statement, regions) = sealed.into_marked_parts();
        let mut statements = vec![statement];
        let declaration = CStmt::comment("declaration");

        assert_eq!(
            insert_region_declarations(&mut statements, &regions, target, &[declaration]),
            1
        );
        let CStmt::StructuredRegion { stmt: root, .. } = &statements[0] else {
            panic!("function marker")
        };
        let CStmt::Block(children) = root.as_ref() else {
            panic!("function body")
        };
        let CStmt::StructuredRegion { stmt: first, .. } = &children[0] else {
            panic!("first marker")
        };
        let CStmt::StructuredRegion { stmt: second, .. } = &children[1] else {
            panic!("second marker")
        };
        assert!(!format!("{first:?}").contains("declaration"));
        assert!(format!("{second:?}").contains("declaration"));
    }

    #[test]
    fn inline_replaces_only_the_exact_marked_assignment() {
        let symbols = std::rc::Rc::new(std::cell::RefCell::new(SymbolTable::new()));
        let symbol =
            symbols
                .borrow_mut()
                .declare("value", crate::ast::CType::UInt(32), SymbolRole::Carrier);
        let marker = observation(7);
        let assignment = CStmt::observed(
            marker,
            CStmt::expr(CExpr::assign(CExpr::Var(symbol), CExpr::UIntLit(9))),
        );
        let mut statements = vec![assignment, CStmt::comment("untouched")];

        assert_eq!(
            inline_exact_write(
                &mut statements,
                marker,
                symbol,
                &crate::ast::CType::UInt(32),
            ),
            1
        );
        assert!(matches!(
            statements[0].unobserved(),
            CStmt::Decl {
                name,
                init: Some(CExpr::UIntLit(9)),
                ..
            } if *name == symbol
        ));
    }

    #[test]
    fn final_scope_order_matches_do_while_execution() {
        let body_id = observation(0);
        let condition_id = observation(1);
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::DoWhile {
                body: Box::new(CStmt::observed(body_id, CStmt::Empty)),
                cond: CExpr::observed(condition_id, CExpr::UIntLit(1)),
            },
        ))
        .expect("sealed do-while");
        let (statement, regions) = sealed.into_marked_parts();
        let scopes = collect_final_observation_scopes(&[statement], &regions, 2);
        let order_of = |index| match scopes[index] {
            Some(FinalObservationScope::Exact { order, .. }) => order,
            other => panic!("expected exact scope, got {other:?}"),
        };
        assert!(order_of(0) < order_of(1));
    }

    #[test]
    fn final_scope_order_matches_for_execution_phases() {
        let init_id = observation(0);
        let condition_id = observation(1);
        let body_id = observation(2);
        let update_id = observation(3);
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::For {
                init: Some(Box::new(CStmt::observed(init_id, CStmt::Empty))),
                cond: Some(CExpr::observed(condition_id, CExpr::UIntLit(1))),
                update: Some(CExpr::observed(update_id, CExpr::UIntLit(0))),
                body: Box::new(CStmt::observed(body_id, CStmt::Empty)),
            },
        ))
        .expect("sealed for");
        let (statement, regions) = sealed.into_marked_parts();
        let scopes = collect_final_observation_scopes(&[statement], &regions, 4);
        let order_of = |index| match scopes[index] {
            Some(FinalObservationScope::Exact { order, .. }) => order,
            other => panic!("expected exact scope, got {other:?}"),
        };
        assert!(order_of(0) < order_of(1));
        assert!(order_of(1) < order_of(2));
        assert!(order_of(2) < order_of(3));
    }
}
