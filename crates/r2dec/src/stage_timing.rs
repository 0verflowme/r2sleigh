//! Where one render's time goes, when asked.
//!
//! The engine times the whole render as one phase, and on a corpus cell that
//! phase is about ninety-five per cent of everything the engine does. That
//! number says the rewriting layer is in the right place and nothing about
//! which part of the render to change: the binding plan, the fold, the
//! structuring, the normalization passes, declaration placement, the seal and
//! code generation are one bucket.
//!
//! This is a diagnostic, not a contract. It writes to stderr under
//! `R2SLEIGH_TIMING`, the same switch the engine's phase comment uses, and it
//! is a thread-local so a stage can be marked from wherever it actually
//! happens rather than from wherever a timing struct could be threaded. It
//! costs one `Instant::now` per mark when the switch is off and nothing else.

use std::cell::RefCell;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("R2SLEIGH_TIMING").is_some())
}

thread_local! {
    static STAGES: RefCell<Vec<(&'static str, Duration)>> = const { RefCell::new(Vec::new()) };
    static LAST: RefCell<Option<Instant>> = const { RefCell::new(None) };
}

/// Begin a render. Any marks left by an earlier render are discarded, because
/// a render that stopped early owes nothing to the next one.
pub(crate) fn begin() {
    if !enabled() {
        return;
    }
    STAGES.with_borrow_mut(Vec::clear);
    LAST.with_borrow_mut(|last| *last = Some(Instant::now()));
}

/// Close the stage that has been running and name it.
pub(crate) fn mark(stage: &'static str) {
    if !enabled() {
        return;
    }
    let now = Instant::now();
    let elapsed = LAST.with_borrow_mut(|last| {
        let elapsed = last.map(|start| now.duration_since(start));
        *last = Some(now);
        elapsed
    });
    if let Some(elapsed) = elapsed {
        STAGES.with_borrow_mut(|stages| {
            // A stage reached twice is one stage: structuring runs again when a
            // speculative rewrite declines, and two rows for one name would
            // read as two different stages.
            if let Some(row) = stages.iter_mut().find(|(name, _)| *name == stage) {
                row.1 += elapsed;
            } else {
                stages.push((stage, elapsed));
            }
        });
    }
}

/// Report the render just finished, once, to stderr.
pub(crate) fn report(function: &str) {
    if !enabled() {
        return;
    }
    let stages = STAGES.with_borrow_mut(std::mem::take);
    LAST.with_borrow_mut(|last| *last = None);
    if stages.is_empty() {
        return;
    }
    let total: Duration = stages.iter().map(|(_, elapsed)| *elapsed).sum();
    let mut line = format!(
        "r2dec stage timing {function}: total={}us",
        total.as_micros()
    );
    for (stage, elapsed) in &stages {
        line.push_str(&format!(" {stage}={}us", elapsed.as_micros()));
    }
    eprintln!("{line}");
}
