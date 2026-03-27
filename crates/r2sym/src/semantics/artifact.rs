use serde::{Deserialize, Serialize};

use crate::sim::DerivedSummaryDiagnostics;

use super::facts::SymbolicFunctionFacts;
use super::vm::{InterpreterDispatchSummary, VmStepSummary};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticMode {
    Raw,
    Compiled,
    Residual,
    VmSummary,
}

pub type CompiledSemanticMode = SemanticMode;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SliceClass {
    Wrapper,
    Worker,
    RecursiveGroup,
    InterpreterSwitch,
    InterpreterIndirect,
    GenericLarge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ResidualReason {
    MissingArch,
    LargeCfg,
    SummaryBudgetExhausted,
    SccBudgetExhausted,
    InterpreterRequiresStepSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticCapability {
    pub query_ready: bool,
    pub type_ready: bool,
    pub decompile_ready: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSemanticArtifact {
    pub mode: SemanticMode,
    pub slice_class: SliceClass,
    pub capability: SemanticCapability,
    pub residual_reasons: Vec<ResidualReason>,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub derived_diagnostics: DerivedSummaryDiagnostics,
    pub symbolic_facts: SymbolicFunctionFacts,
    pub interpreter: Option<InterpreterDispatchSummary>,
    pub vm_step: Option<VmStepSummary>,
    pub cache_hit: bool,
}

pub type CompiledFunctionSemantics = CompiledSemanticArtifact;
