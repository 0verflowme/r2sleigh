pub struct Signature;
pub struct Projection;

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

fn canonical_owner_may_use_name_registry(name: &str) {
    let _ = signature_hint_for_name_candidates([name], 0);
    let _ = signature_hint_for_role_name(name, 0);
    let _ = type_projection_for_name_candidates([name], 0);
}

fn main() {}
