//! Cooperative control for decompiler inner work.

use r2ssa::{SsaExecutionStopReason, SsaWorkControl};

/// Decompiler phase in which cooperative execution stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DecompileWorkPhase {
    Normalization,
    Structuring,
    Rendering,
}

/// Distinct cooperative stop returned before any partial AST or C escapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DecompileExecutionStop {
    phase: DecompileWorkPhase,
    reason: SsaExecutionStopReason,
}

impl DecompileExecutionStop {
    pub const fn new(phase: DecompileWorkPhase, reason: SsaExecutionStopReason) -> Self {
        Self { phase, reason }
    }

    pub const fn phase(self) -> DecompileWorkPhase {
        self.phase
    }

    pub const fn reason(self) -> SsaExecutionStopReason {
        self.reason
    }
}

impl std::fmt::Display for DecompileExecutionStop {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "decompiler {:?} stopped: {}",
            self.phase, self.reason
        )
    }
}

impl std::error::Error for DecompileExecutionStop {}

/// Copyable phase wrapper around the allocation-free SSA polling seam.
#[derive(Clone, Copy)]
pub struct DecompileWorkControl<'a> {
    control: &'a dyn SsaWorkControl,
    phase: DecompileWorkPhase,
}

impl<'a> DecompileWorkControl<'a> {
    pub const fn new(control: &'a dyn SsaWorkControl, phase: DecompileWorkPhase) -> Self {
        Self { control, phase }
    }

    pub const fn phase(self) -> DecompileWorkPhase {
        self.phase
    }

    pub const fn with_phase(self, phase: DecompileWorkPhase) -> Self {
        Self {
            control: self.control,
            phase,
        }
    }

    #[inline]
    pub fn poll(self) -> Result<(), DecompileExecutionStop> {
        self.control
            .poll()
            .map_err(|reason| DecompileExecutionStop::new(self.phase, reason))
    }

    pub(crate) const fn raw(self) -> &'a dyn SsaWorkControl {
        self.control
    }
}
