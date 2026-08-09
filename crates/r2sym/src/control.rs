//! Cooperative cancellation and deadline control for symbolic execution.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

/// Cloneable cancellation token shared by symbolic execution workers.
#[derive(Debug, Clone, Default)]
pub struct SymCancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl SymCancellationToken {
    /// Request cooperative cancellation.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }

    /// Whether cancellation has been requested.
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }
}

/// Why a symbolic operation stopped before its semantic result was complete.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymExecutionStopReason {
    Cancelled,
    DeadlineExceeded,
}

impl std::fmt::Display for SymExecutionStopReason {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Cancelled => "symbolic execution cancelled",
            Self::DeadlineExceeded => "symbolic execution deadline exceeded",
        })
    }
}

impl std::error::Error for SymExecutionStopReason {}

/// Cooperative execution control shared by path, executor, and solver worklists.
///
/// Cancellation is polled before and after Z3 calls, but a token set while Z3 is
/// inside one check does not interrupt that check. Deadlines remain bounded
/// because the solver reapplies the remaining deadline as a Z3 timeout before
/// every check. Callers that require bounded in-flight cancellation should pair
/// cancellation with a deadline until a lifecycle-safe solver interrupt owner
/// is available.
#[derive(Debug, Clone, Default)]
pub struct SymExecutionControl {
    cancellation: SymCancellationToken,
    deadline: Option<Instant>,
}

impl SymExecutionControl {
    /// Build a control that can observe both cancellation and a deadline.
    pub fn new(cancellation: SymCancellationToken, deadline: Option<Instant>) -> Self {
        Self {
            cancellation,
            deadline,
        }
    }

    pub fn with_cancellation(cancellation: SymCancellationToken) -> Self {
        Self::new(cancellation, None)
    }

    pub fn with_deadline(deadline: Instant) -> Self {
        Self::new(SymCancellationToken::default(), Some(deadline))
    }

    pub fn with_timeout(timeout: Duration) -> Self {
        Self::with_deadline(
            Instant::now()
                .checked_add(timeout)
                .unwrap_or_else(Instant::now),
        )
    }

    pub fn cancellation(&self) -> SymCancellationToken {
        self.cancellation.clone()
    }

    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    pub fn stop_reason(&self) -> Option<SymExecutionStopReason> {
        if self.cancellation.is_cancelled() {
            return Some(SymExecutionStopReason::Cancelled);
        }
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
            .then_some(SymExecutionStopReason::DeadlineExceeded)
    }

    pub fn poll(&self) -> Result<(), SymExecutionStopReason> {
        self.stop_reason().map_or(Ok(()), Err)
    }

    /// Milliseconds remaining until the deadline, rounded up for solver APIs.
    pub(crate) fn remaining_timeout_ms(&self) -> Option<u32> {
        let remaining = self.deadline?.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Some(1);
        }
        Some(
            remaining
                .as_millis()
                .saturating_add(1)
                .min(u32::MAX as u128) as u32,
        )
    }
}
