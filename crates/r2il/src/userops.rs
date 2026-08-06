//! Shared semantic identifiers for architecture-specific `CallOther` userops.
//!
//! These IDs are reserved for r2sleigh lift-time repairs and are intentionally
//! outside normal Sleigh-assigned pcodeop indexes, which are dense small values.

/// ARM64 pointer authentication operation that authenticates a pointer.
pub const ARM64_PAUTH_AUTH_USEROP: u32 = 0xffff_0001;
/// ARM64 pointer authentication operation that signs a pointer.
pub const ARM64_PAUTH_SIGN_USEROP: u32 = 0xffff_0002;
/// ARM64 pointer authentication operation that strips pointer authentication.
pub const ARM64_PAUTH_STRIP_USEROP: u32 = 0xffff_0003;

/// Returns true for synthetic ARM64 pointer-authentication userops.
pub const fn is_arm64_pauth_userop(userop: u32) -> bool {
    matches!(
        userop,
        ARM64_PAUTH_AUTH_USEROP | ARM64_PAUTH_SIGN_USEROP | ARM64_PAUTH_STRIP_USEROP
    )
}
