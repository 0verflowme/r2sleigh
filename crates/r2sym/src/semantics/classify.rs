use r2ssa::SsaArtifact;

use super::artifact::SliceClass;
use super::vm::{InterpreterDispatchSummary, InterpreterKind};

pub(super) fn classify_slice(
    func: &SsaArtifact,
    helper_functions: usize,
    interpreter: Option<&InterpreterDispatchSummary>,
    strong_vm_step: bool,
) -> SliceClass {
    if strong_vm_step && let Some(interpreter) = interpreter {
        return match interpreter.kind {
            InterpreterKind::SwitchDispatch => SliceClass::InterpreterSwitch,
            InterpreterKind::IndirectDispatch => SliceClass::InterpreterIndirect,
        };
    }

    let cfg = func.function().cfg_risk_summary();
    if cfg.block_count <= 12 && cfg.loop_count == 0 && helper_functions <= 2 {
        return SliceClass::Wrapper;
    }
    if cfg.block_count > 64 || cfg.loop_count > 0 || helper_functions > 3 {
        return SliceClass::Worker;
    }
    SliceClass::GenericLarge
}
