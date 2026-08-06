mod role_registry {
    pub struct Signature;
    pub struct Projection;
    pub struct RoleIdentity;

    pub fn signature_hint_for_name_candidates<const N: usize>(
        _: [&str; N],
        _: usize,
    ) -> Option<Signature> {
        None
    }

    pub fn signature_hint_for_role_name(_: &str, _: usize) -> Option<Signature> {
        None
    }

    pub fn type_projection_for_name_candidates<const N: usize>(
        _: [&str; N],
        _: usize,
    ) -> Option<Projection> {
        None
    }

    pub fn signature_hint_for_role_identity(_: &RoleIdentity, _: usize) -> Option<Signature> {
        None
    }
}

fn bad_name_candidate_projection(name: &str) {
    let _ = role_registry::signature_hint_for_name_candidates([name], 0);
}

fn bad_direct_role_name_projection(name: &str) {
    let _ = role_registry::signature_hint_for_role_name(name, 0);
}

fn bad_type_projection_from_names(name: &str) {
    let _ = role_registry::type_projection_for_name_candidates([name], 0);
}

fn good_role_identity_projection(role: &role_registry::RoleIdentity) {
    let _ = role_registry::signature_hint_for_role_identity(role, 0);
}

fn main() {}
