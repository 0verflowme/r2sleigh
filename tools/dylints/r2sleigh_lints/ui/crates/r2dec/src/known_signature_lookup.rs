use std::collections::BTreeMap;

#[derive(Clone)]
struct SignatureMaps {
    inner: BTreeMap<String, usize>,
}

struct Inputs {
    known_function_signatures: BTreeMap<String, usize>,
    nested: SignatureMaps,
}

struct NestedInputs {
    known_function_signatures: SignatureMaps,
}

fn main() {
    let mut inputs = Inputs {
        known_function_signatures: BTreeMap::new(),
        nested: SignatureMaps {
            inner: BTreeMap::new(),
        },
    };
    let mut nested_inputs = NestedInputs {
        known_function_signatures: SignatureMaps {
            inner: BTreeMap::new(),
        },
    };
    inputs
        .known_function_signatures
        .insert("printf".to_owned(), 2);
    inputs.nested.inner.insert("puts".to_owned(), 1);
    nested_inputs
        .known_function_signatures
        .inner
        .insert("scanf".to_owned(), 3);

    let ordinary_map = BTreeMap::<String, usize>::new();
    let _ = ordinary_map.get("printf");
    let _ = inputs.known_function_signatures.get("printf");
    let _ = inputs.known_function_signatures.clone().get("printf");
    let _ = (&inputs.known_function_signatures).get("printf");
    let _ = inputs.nested.inner.get("puts");
    let _ = nested_inputs.known_function_signatures.inner.get("scanf");
}
