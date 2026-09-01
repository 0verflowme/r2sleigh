//! What the predicate that refused was looking at.
//!
//! A refusal already records where it was decided, and where is never the
//! question. Every investigation into one starts the same way: print the
//! operands the failing predicate compared, then read the code around them.
//! Four separate defects were found that way in one session, each by adding a
//! temporary `eprintln` and removing it again, which is four chances to
//! instrument the wrong branch and four probes that taught the next reader
//! nothing.
//!
//! So the operands stay. `refusal_evidence!` prints them under
//! `R2DEC_TRACE_REFUSAL`, beside the refusal's own line, and costs nothing when
//! the variable is unset: the arguments live inside the macro body and are
//! never evaluated.
//!
//! This is deliberately a diagnostic channel and not a payload the refusal
//! carries. What travels with a refusal is its static site name, which is free
//! and reaches the reader through the rendered comment; what the predicate saw
//! is unbounded, per-function, and only wanted when someone is looking.

use std::sync::OnceLock;

/// Whether refusal tracing is on.
///
/// Read once. The predicates this guards sit in loops over every value in a
/// function, and an environment lookup per refusal was measurable.
pub(crate) fn tracing() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("R2DEC_TRACE_REFUSAL").is_some())
}

/// Print the operands of a predicate that is about to refuse.
///
/// `file!()` and `line!()` expand at the call site, so the location names the
/// predicate rather than whatever called it.
macro_rules! refusal_evidence {
    ($predicate:literal, $($operands:tt)*) => {
        if $crate::refusal_evidence::tracing() {
            ::std::eprintln!(
                "refusal evidence {} at {}:{}: {}",
                $predicate,
                ::std::file!(),
                ::std::line!(),
                ::std::format_args!($($operands)*)
            );
        }
    };
}

pub(crate) use refusal_evidence;
