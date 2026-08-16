//! Canonical semantic graph and fact-planning scaffolding.
//!
//! This module is intentionally small for the first architecture tranche: it
//! gives SSA, symex, runtime, and future replay backends a typed place to meet
//! without putting semantic policy in the plugin or executor.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use r2ssa::InterprocFunctionId;

use crate::PreparedFunctionScope;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdgeId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegionId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactPrecision {
    Unknown,
    UnderApprox,
    Residual,
    OverApprox,
    Exact,
}

impl FactPrecision {
    pub fn is_exact(self) -> bool {
        matches!(self, Self::Exact)
    }

    pub fn is_residual_or_weaker(self) -> bool {
        matches!(self, Self::Unknown | Self::UnderApprox | Self::Residual)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemanticEvidenceKind {
    Static,
    Runtime,
    Replay,
    UserAssumption,
    Inferred,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticEvidenceRecord {
    pub kind: SemanticEvidenceKind,
    pub precision: FactPrecision,
    pub reason: String,
}

impl SemanticEvidenceRecord {
    pub fn exact_static(reason: impl Into<String>) -> Self {
        Self {
            kind: SemanticEvidenceKind::Static,
            precision: FactPrecision::Exact,
            reason: reason.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticNodeKind {
    FunctionEntry {
        function: FunctionId,
    },
    BasicBlock {
        function: FunctionId,
        addr: u64,
    },
    RuntimeRegion {
        region: RegionId,
        base: u64,
        size: u64,
    },
    ExceptionContinuation {
        handler: u64,
    },
    ReplayCheckpoint {
        checkpoint: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticNode {
    pub id: NodeId,
    pub kind: SemanticNodeKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticEdgeKind {
    Cfg,
    Call,
    Return,
    Thunk,
    Exception,
    RuntimeAlias,
    Replay,
    Summary,
    Refused { reason: String },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallEdgePolicy {
    FallthroughOnly,
    InlineCallee,
    ApplySummary,
    ForkCallAndFallthrough,
    Refuse,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticEdgeAction {
    Follow,
    ApplyCallPolicy(CallEdgePolicy),
    SeedContinuation,
    MapRuntimeRegion,
    ApplySummary,
    Refuse { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticEdge {
    pub id: EdgeId,
    pub from: NodeId,
    pub to: NodeId,
    pub kind: SemanticEdgeKind,
    pub action: SemanticEdgeAction,
    pub evidence: SemanticEvidenceRecord,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeRegionFact {
    pub id: RegionId,
    pub base: u64,
    pub size: u64,
    pub source_base: Option<u64>,
    pub executable: bool,
    pub evidence: SemanticEvidenceRecord,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteStopReason {
    Completed,
    HitTarget(u64),
    Exception(u64),
    BudgetExceeded,
    Unsupported(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ConcreteTraceEvidence {
    pub executed_blocks: Vec<u64>,
    pub runtime_regions: Vec<RuntimeRegionFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteMemorySeed {
    pub addr: u64,
    pub bytes: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteRunRequest {
    pub entry: u64,
    pub target: Option<u64>,
    pub max_instructions: usize,
    pub argv: Vec<Vec<u8>>,
    pub registers: BTreeMap<String, u64>,
    pub memory: Vec<ConcreteMemorySeed>,
    pub runtime_regions: Vec<RuntimeRegionFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteRunResult {
    pub trace: ConcreteTraceEvidence,
    pub stop_reason: ConcreteStopReason,
    pub final_pc: Option<u64>,
    pub diagnostics: Vec<String>,
}

pub trait ConcreteExecutionBackend {
    fn run(&self, request: ConcreteRunRequest) -> ConcreteRunResult;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunctionClosureBudget {
    pub max_functions: usize,
    pub max_blocks_per_function: usize,
    pub max_total_blocks: usize,
}

impl Default for FunctionClosureBudget {
    fn default() -> Self {
        Self {
            max_functions: 32,
            max_blocks_per_function: 96,
            max_total_blocks: 512,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionClosureReason {
    Root,
    HelperByScope,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionClosureExclusionReason {
    FunctionBudgetExceeded,
    BlockBudgetExceeded,
    TotalBlockBudgetExceeded,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionClosureEntry {
    pub function: FunctionId,
    pub name: Option<String>,
    pub block_count: usize,
    pub reason: FunctionClosureReason,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionClosureExclusion {
    pub function: FunctionId,
    pub name: Option<String>,
    pub block_count: usize,
    pub reason: FunctionClosureExclusionReason,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionClosurePlan {
    pub root: FunctionId,
    pub budget: FunctionClosureBudget,
    pub included: Vec<FunctionClosureEntry>,
    pub excluded: Vec<FunctionClosureExclusion>,
}

impl FunctionClosurePlan {
    pub fn from_scope(scope: &PreparedFunctionScope, budget: FunctionClosureBudget) -> Self {
        let root = FunctionId(scope.root_id().0);
        let mut total_blocks = 0usize;
        let mut included = Vec::new();
        let mut excluded = Vec::new();

        for function in scope.functions().values() {
            let id = FunctionId(function.id.0);
            let block_count = function.prepared.cfg().num_blocks();
            let is_root = function.id == InterprocFunctionId(root.0);
            let exclusion = if !is_root && included.len() >= budget.max_functions {
                Some(FunctionClosureExclusionReason::FunctionBudgetExceeded)
            } else if !is_root && block_count > budget.max_blocks_per_function {
                Some(FunctionClosureExclusionReason::BlockBudgetExceeded)
            } else if !is_root && total_blocks.saturating_add(block_count) > budget.max_total_blocks
            {
                Some(FunctionClosureExclusionReason::TotalBlockBudgetExceeded)
            } else {
                None
            };

            if let Some(reason) = exclusion {
                excluded.push(FunctionClosureExclusion {
                    function: id,
                    name: function.name.clone(),
                    block_count,
                    reason,
                });
                continue;
            }

            total_blocks = total_blocks.saturating_add(block_count);
            included.push(FunctionClosureEntry {
                function: id,
                name: function.name.clone(),
                block_count,
                reason: if is_root {
                    FunctionClosureReason::Root
                } else {
                    FunctionClosureReason::HelperByScope
                },
            });
        }

        Self {
            root,
            budget,
            included,
            excluded,
        }
    }

    pub fn included_ids(&self) -> BTreeSet<FunctionId> {
        self.included
            .iter()
            .map(|entry| entry.function)
            .collect::<BTreeSet<_>>()
    }
}

#[derive(Debug, Clone, Default)]
pub struct SemanticProgramGraph {
    nodes: BTreeMap<NodeId, SemanticNode>,
    edges: BTreeMap<EdgeId, SemanticEdge>,
    block_nodes: BTreeMap<(FunctionId, u64), NodeId>,
    addr_nodes: BTreeMap<u64, BTreeSet<NodeId>>,
    successors: BTreeMap<NodeId, BTreeSet<NodeId>>,
    predecessors: BTreeMap<NodeId, BTreeSet<NodeId>>,
    next_node: u64,
    next_edge: u64,
}

impl SemanticProgramGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_scope(scope: &PreparedFunctionScope, closure: &FunctionClosurePlan) -> Self {
        let mut graph = Self::new();
        let included = closure.included_ids();
        for function in scope.functions().values() {
            let function_id = FunctionId(function.id.0);
            if !included.contains(&function_id) {
                continue;
            }
            graph.add_node(SemanticNodeKind::FunctionEntry {
                function: function_id,
            });
            for addr in function.prepared.cfg().block_addrs() {
                graph.add_block_node(function_id, addr);
            }
        }

        for function in scope.functions().values() {
            let function_id = FunctionId(function.id.0);
            if !included.contains(&function_id) {
                continue;
            }
            for addr in function.prepared.cfg().block_addrs() {
                let Some(block) = function.prepared.cfg().get_block(addr) else {
                    continue;
                };
                for succ in block.successors() {
                    graph.add_block_edge(
                        function_id,
                        addr,
                        function_id,
                        succ,
                        SemanticEdgeKind::Cfg,
                        SemanticEdgeAction::Follow,
                    );
                }
            }
            for call in function.prepared.call_sites().by_id.values() {
                let Some(target) = function.prepared.resolved_call_target(call) else {
                    continue;
                };
                let Some((block_addr, _)) = function.prepared.inst_op_site(call.at) else {
                    continue;
                };
                let callee_id = scope
                    .function_containing_block(target)
                    .map(|callee| FunctionId(callee.id.0))
                    .unwrap_or(FunctionId(target));
                graph.add_block_edge(
                    function_id,
                    block_addr,
                    callee_id,
                    target,
                    SemanticEdgeKind::Call,
                    SemanticEdgeAction::ApplyCallPolicy(CallEdgePolicy::ForkCallAndFallthrough),
                );
            }
        }
        graph
    }

    pub fn nodes(&self) -> &BTreeMap<NodeId, SemanticNode> {
        &self.nodes
    }

    pub fn edges(&self) -> &BTreeMap<EdgeId, SemanticEdge> {
        &self.edges
    }

    pub fn node_for_block(&self, function: FunctionId, addr: u64) -> Option<NodeId> {
        self.block_nodes.get(&(function, addr)).copied()
    }

    pub fn nodes_for_addr(&self, addr: u64) -> Option<&BTreeSet<NodeId>> {
        self.addr_nodes.get(&addr)
    }

    pub fn reverse_reachable_nodes(&self, target: NodeId) -> BTreeSet<NodeId> {
        let mut seen = BTreeSet::new();
        let mut queue = VecDeque::from([target]);
        while let Some(node) = queue.pop_front() {
            if !seen.insert(node) {
                continue;
            }
            for pred in self.predecessors.get(&node).into_iter().flatten() {
                queue.push_back(*pred);
            }
        }
        seen
    }

    fn add_node(&mut self, kind: SemanticNodeKind) -> NodeId {
        let id = NodeId(self.next_node);
        self.next_node = self.next_node.saturating_add(1);
        if let SemanticNodeKind::BasicBlock { function, addr } = kind {
            self.block_nodes.insert((function, addr), id);
            self.addr_nodes.entry(addr).or_default().insert(id);
            self.nodes.insert(id, SemanticNode { id, kind });
            return id;
        }
        self.nodes.insert(id, SemanticNode { id, kind });
        id
    }

    fn add_block_node(&mut self, function: FunctionId, addr: u64) -> NodeId {
        if let Some(id) = self.node_for_block(function, addr) {
            return id;
        }
        self.add_node(SemanticNodeKind::BasicBlock { function, addr })
    }

    fn add_block_edge(
        &mut self,
        from_function: FunctionId,
        from_addr: u64,
        to_function: FunctionId,
        to_addr: u64,
        kind: SemanticEdgeKind,
        action: SemanticEdgeAction,
    ) -> EdgeId {
        let from = self.add_block_node(from_function, from_addr);
        let to = self.add_block_node(to_function, to_addr);
        let id = EdgeId(self.next_edge);
        self.next_edge = self.next_edge.saturating_add(1);
        self.successors.entry(from).or_default().insert(to);
        self.predecessors.entry(to).or_default().insert(from);
        self.edges.insert(
            id,
            SemanticEdge {
                id,
                from,
                to,
                kind,
                action,
                evidence: SemanticEvidenceRecord::exact_static("scope graph"),
            },
        );
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
    use r2ssa::SsaArtifact;

    fn make_const(val: u64) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size: 8,
            meta: None,
        }
    }

    fn leaf(addr: u64) -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("leaf SSA")
    }

    #[test]
    fn closure_plan_is_deterministic_and_budgeted() {
        let root = leaf(0x1000);
        let helper_a = leaf(0x2000);
        let helper_b = leaf(0x3000);
        let scope = PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x3000),
                    name: Some("helper_b".to_string()),
                    prepared: std::sync::Arc::new(helper_b),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: std::sync::Arc::new(root),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("helper_a".to_string()),
                    prepared: std::sync::Arc::new(helper_a),
                },
            ],
        )
        .expect("scope");

        let plan = FunctionClosurePlan::from_scope(
            &scope,
            FunctionClosureBudget {
                max_functions: 2,
                ..FunctionClosureBudget::default()
            },
        );

        assert_eq!(
            plan.included
                .iter()
                .map(|entry| entry.function.0)
                .collect::<Vec<_>>(),
            vec![0x1000, 0x2000]
        );
        assert_eq!(plan.excluded.len(), 1);
        assert_eq!(
            plan.excluded[0].reason,
            FunctionClosureExclusionReason::FunctionBudgetExceeded
        );
    }

    #[test]
    fn graph_reverse_reachability_is_indexed_by_nodes() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1004),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let root = SsaArtifact::for_symbolic(&blocks, None).expect("root SSA");
        let scope = PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: std::sync::Arc::new(root),
            }],
        )
        .expect("scope");
        let closure = FunctionClosurePlan::from_scope(&scope, FunctionClosureBudget::default());
        let graph = SemanticProgramGraph::from_scope(&scope, &closure);
        let target = graph
            .node_for_block(FunctionId(0x1000), 0x1004)
            .expect("target node");

        let reachable = graph.reverse_reachable_nodes(target);
        assert!(reachable.contains(&target));
        assert!(
            reachable.contains(
                &graph
                    .node_for_block(FunctionId(0x1000), 0x1000)
                    .expect("entry node")
            )
        );
    }
}
