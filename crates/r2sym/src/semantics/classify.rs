use r2ssa::SsaArtifact;

use crate::sim::DerivedSummaryDiagnostics;

use super::artifact::SliceClass;
use super::vm::{InterpreterDispatchSummary, InterpreterKind};

pub(super) fn classify_slice(
    func: &SsaArtifact,
    helper_functions: usize,
    derived_diagnostics: &DerivedSummaryDiagnostics,
    interpreter: Option<&InterpreterDispatchSummary>,
) -> SliceClass {
    if let Some(interpreter) = interpreter {
        return match interpreter.kind {
            InterpreterKind::SwitchDispatch => SliceClass::InterpreterSwitch,
            InterpreterKind::IndirectDispatch => SliceClass::InterpreterIndirect,
        };
    }

    let cfg = func.function().cfg_risk_summary();
    if derived_diagnostics.max_scc_size > 1 {
        return SliceClass::RecursiveGroup;
    }
    if cfg.block_count <= 12 && cfg.loop_count == 0 && helper_functions <= 2 {
        return SliceClass::Wrapper;
    }
    if cfg.block_count > 64 || cfg.loop_count > 0 || helper_functions > 3 {
        return SliceClass::Worker;
    }
    SliceClass::GenericLarge
}
