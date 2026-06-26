struct Prepared;

struct Function;

struct PredicateFacts {
    predicates: (),
    switches: (),
}

struct Inputs {
    prepared_predicates: PredicateFacts,
}

impl Prepared {
    fn predicates(&self) -> PredicateFacts {
        PredicateFacts {
            predicates: (),
            switches: (),
        }
    }

    fn function(&self) -> Function {
        Function
    }
}

impl Function {
    fn infer_switch_selector_var(&self, _block: u64) {}
}

fn main() {
    let prepared = Prepared;
    let inputs = Inputs {
        prepared_predicates: prepared.predicates(),
    };
    let _ = &prepared.predicates().predicates;
    let _ = &prepared.predicates().switches;
    let _ = &inputs.prepared_predicates;
    let _ = prepared.function().infer_switch_selector_var(0x1000);
}
