//! Conversion from canonical type facts to renderer AST types.

/// Convert a shared-model type into the AST's type.
///
/// This was a second copy of the conversion in `lib.rs`, and the two had
/// already drifted: this one turned every function type into `Unknown` while
/// the other kept its signature. One conversion now, so they cannot disagree
/// again.
pub(crate) use crate::type_like_to_ctype;
