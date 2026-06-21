struct Facts;
struct Identity;

impl Facts {
    fn identity_for_callsite(&self) -> Option<Identity> {
        Some(Identity)
    }

    fn identity_for_direct_addr(&self) -> Option<Identity> {
        Some(Identity)
    }

    fn target_policy_for_callsite_or_identity(&self) -> Option<()> {
        Some(())
    }
}

impl Identity {
    fn is_import_policy_authorized(&self) -> bool {
        false
    }

    fn from_direct_target() -> Self {
        Self
    }
}

fn callee_name_is_import_like(_: &str) -> bool {
    false
}

fn main() {
    let facts = Facts;
    let identity = Identity;
    let _ = facts.identity_for_callsite();
    let _ = facts.identity_for_direct_addr();
    let _ = facts.target_policy_for_callsite_or_identity();
    let _ = identity.is_import_policy_authorized();
    let _ = Identity::from_direct_target();
    let _ = callee_name_is_import_like("sym.imp.printf");
}
