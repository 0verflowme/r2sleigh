struct CallSite {
    direct_target: Option<u64>,
}

struct Ssa;

impl Ssa {
    fn resolved_call_target(&self, _: &CallSite) -> Option<u64> {
        Some(0x401000)
    }
}

fn main() {
    let call = CallSite {
        direct_target: Some(0x401000),
    };
    let ssa = Ssa;
    let _ = call.direct_target;
    let _ = ssa.resolved_call_target(&call);
}
