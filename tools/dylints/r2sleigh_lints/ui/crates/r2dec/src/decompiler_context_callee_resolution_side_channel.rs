struct CalleeResolutionFacts;

struct DecompilerContext {
    callee_resolution: Option<CalleeResolutionFacts>,
}

impl DecompilerContext {
    fn with_callee_resolution(self, _facts: Option<CalleeResolutionFacts>) -> Self {
        self
    }
}

fn main() {
    let ctx = DecompilerContext {
        callee_resolution: None,
    };
    let _ = ctx.with_callee_resolution(None);
}
