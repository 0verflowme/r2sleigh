//! Cooperative control for bounded SSA preparation work.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

/// Cloneable cancellation token shared by SSA preparation callers.
#[derive(Debug, Clone, Default)]
pub struct SsaCancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl SsaCancellationToken {
    /// Request cooperative cancellation.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }

    /// Whether cancellation has been requested.
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }
}

/// Why controlled SSA preparation stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SsaExecutionStopReason {
    Cancelled,
    DeadlineExceeded,
}

impl std::fmt::Display for SsaExecutionStopReason {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Cancelled => "SSA preparation cancelled",
            Self::DeadlineExceeded => "SSA preparation deadline exceeded",
        })
    }
}

impl std::error::Error for SsaExecutionStopReason {}

/// Error returned by checked SSA builders.
///
/// Malformed source input remains distinct from cooperative cancellation and
/// deadline expiry. Optimization iteration caps are normal, valid completion
/// bounds and are still reported through [`crate::OptimizationStats`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SsaPrepareError {
    MalformedInput,
    Cancelled,
    DeadlineExceeded,
}

impl std::fmt::Display for SsaPrepareError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::MalformedInput => "malformed SSA source input",
            Self::Cancelled => "SSA preparation cancelled",
            Self::DeadlineExceeded => "SSA preparation deadline exceeded",
        })
    }
}

impl std::error::Error for SsaPrepareError {}

impl From<SsaExecutionStopReason> for SsaPrepareError {
    fn from(reason: SsaExecutionStopReason) -> Self {
        match reason {
            SsaExecutionStopReason::Cancelled => Self::Cancelled,
            SsaExecutionStopReason::DeadlineExceeded => Self::DeadlineExceeded,
        }
    }
}

/// Allocation-free polling seam used by checked SSA worklists.
///
/// The trait permits deterministic callers and tests without requiring a
/// thread, timer callback, or allocation at each poll.
pub trait SsaWorkControl {
    fn poll(&self) -> Result<(), SsaExecutionStopReason>;
}

/// Cloneable cancellation/deadline control for SSA preparation.
#[derive(Debug, Clone, Default)]
pub struct SsaExecutionControl {
    cancellation: SsaCancellationToken,
    deadline: Option<Instant>,
}

impl SsaExecutionControl {
    /// Build a control that observes both cancellation and a deadline.
    pub fn new(cancellation: SsaCancellationToken, deadline: Option<Instant>) -> Self {
        Self {
            cancellation,
            deadline,
        }
    }

    pub fn with_cancellation(cancellation: SsaCancellationToken) -> Self {
        Self::new(cancellation, None)
    }

    pub fn with_deadline(deadline: Instant) -> Self {
        Self::new(SsaCancellationToken::default(), Some(deadline))
    }

    pub fn with_timeout(timeout: Duration) -> Self {
        Self::with_deadline(
            Instant::now()
                .checked_add(timeout)
                .unwrap_or_else(Instant::now),
        )
    }

    pub fn cancellation(&self) -> SsaCancellationToken {
        self.cancellation.clone()
    }

    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    pub fn stop_reason(&self) -> Option<SsaExecutionStopReason> {
        if self.cancellation.is_cancelled() {
            return Some(SsaExecutionStopReason::Cancelled);
        }
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
            .then_some(SsaExecutionStopReason::DeadlineExceeded)
    }
}

impl SsaWorkControl for SsaExecutionControl {
    fn poll(&self) -> Result<(), SsaExecutionStopReason> {
        self.stop_reason().map_or(Ok(()), Err)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct UncheckedSsaWorkControl;

impl SsaWorkControl for UncheckedSsaWorkControl {
    #[inline]
    fn poll(&self) -> Result<(), SsaExecutionStopReason> {
        Ok(())
    }
}
