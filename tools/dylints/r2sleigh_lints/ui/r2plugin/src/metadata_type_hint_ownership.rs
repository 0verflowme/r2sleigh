mod r2il {
    #[allow(dead_code)]
    pub enum ScalarKind {
        SignedInt,
        UnsignedInt,
    }

    #[allow(dead_code)]
    pub enum PointerHint {
        PointerLike,
        Unknown,
    }
}

struct TypeHint;

fn size_to_signed_int_type(size: u32) -> String {
    format!("int{}_t", size * 8)
}

fn scalar_kind_to_type(kind: r2il::ScalarKind, size: u32) -> Option<TypeHint> {
    match kind {
        r2il::ScalarKind::SignedInt => {
            let _ty = size_to_signed_int_type(size);
            Some(TypeHint)
        }
        r2il::ScalarKind::UnsignedInt => Some(TypeHint),
    }
}

fn metadata_type_hint(pointer_hint: r2il::PointerHint) -> Option<TypeHint> {
    if matches!(pointer_hint, r2il::PointerHint::PointerLike) {
        return Some(TypeHint);
    }
    None
}

fn main() {
    let _ = scalar_kind_to_type(r2il::ScalarKind::SignedInt, 8);
    let _ = metadata_type_hint(r2il::PointerHint::Unknown);
}
