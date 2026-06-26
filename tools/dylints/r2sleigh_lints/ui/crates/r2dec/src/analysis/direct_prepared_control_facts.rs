struct Prepared;

struct PredicateFacts {
    predicates: (),
    switches: (),
}

impl Prepared {
    fn predicates(&self) -> PredicateFacts {
        PredicateFacts {
            predicates: (),
            switches: (),
        }
    }
}

fn main() {
    let prepared = Prepared;
    let _ = &prepared.predicates().predicates;
    let _ = &prepared.predicates().switches;
}
