struct Prepared;

struct Certificates {
    call_results: (),
    call_results_by_callsite: (),
}

impl Prepared {
    fn certificates(&self) -> Certificates {
        Certificates {
            call_results: (),
            call_results_by_callsite: (),
        }
    }
}

fn main() {
    let prepared = Prepared;
    let _ = &prepared.certificates().call_results;
    let _ = &prepared.certificates().call_results_by_callsite;
}
