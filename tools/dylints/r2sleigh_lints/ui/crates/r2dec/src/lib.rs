struct CalleeResolutionFacts;

impl CalleeResolutionFacts {
    fn from_direct_call_targets() -> Self {
        Self
    }

    fn identity_for_direct_target_in_context() -> Self {
        Self
    }

    fn identity_for_name_in_context() -> Self {
        Self
    }
}

fn main() {
    let _ = CalleeResolutionFacts::from_direct_call_targets();
    let _ = CalleeResolutionFacts::identity_for_direct_target_in_context();
    let _ = CalleeResolutionFacts::identity_for_name_in_context();
}
