fn classify(name: &str) -> bool {
    name.starts_with("tmp:")
}

fn ordinary(name: &str) -> bool {
    name.starts_with("test_")
}

struct Inputs {
    known_function_signatures: std::collections::BTreeMap<String, String>,
    callee_facts: std::collections::BTreeMap<String, String>,
}

struct Certificate;

impl Certificate {
    fn authorizes_signature_writeback(&self) -> bool {
        true
    }
}

struct ApplyPolicy {
    type_min_confidence: f64,
    rename_min_confidence: f64,
    struct_min_confidence: f64,
}

impl ApplyPolicy {
    fn mutation_min_confidence(&self) -> f64 {
        self.type_min_confidence
    }

    fn effective_threshold(&self) -> f64 {
        self.struct_min_confidence
    }
}

struct CallSite {
    direct_target: Option<u64>,
}

struct DecompilerConfig;

impl DecompilerConfig {
    fn for_arch(_: &str) -> Self {
        Self
    }
}

struct VariableRecovery;

impl VariableRecovery {
    fn new() -> Self {
        Self
    }

    fn new_with_abi(_: &str) -> Self {
        Self
    }
}

impl Inputs {
    fn identity_for_callsite(&self) -> Option<String> {
        None
    }
}

fn from_direct_call_targets() {}

#[allow(non_snake_case)]
fn Return() {}

fn metadata_type_hint() {}

fn main() {
    let _ = classify("tmp:0x1000");
    let _ = ordinary("test_case");
    let _ = "afcfj";
    let inputs = Inputs {
        known_function_signatures: std::collections::BTreeMap::new(),
        callee_facts: std::collections::BTreeMap::new(),
    };
    let _ = inputs.known_function_signatures.get("printf");
    let _ = inputs.callee_facts.contains_key("printf");
    let _ = inputs.identity_for_callsite();
    let _ = from_direct_call_targets();
    let _ = "switch (x)";
    Return();
    metadata_type_hint();

    let certificate = Certificate;
    let _ = certificate.authorizes_signature_writeback();
    let _ = "signature mutation refused: stale certificate";

    let policy = ApplyPolicy {
        type_min_confidence: 0.9,
        rename_min_confidence: 0.8,
        struct_min_confidence: 0.7,
    };
    let _ = policy.mutation_min_confidence();
    let _ = policy.effective_threshold();
    let _ = policy.type_min_confidence;
    let _ = policy.rename_min_confidence;
    let _ = policy.struct_min_confidence;

    let call = CallSite {
        direct_target: Some(0x401000),
    };
    let _ = call.direct_target;
    let _ = DecompilerConfig::for_arch("x86-64");
    let _ = VariableRecovery::new();
    let _ = VariableRecovery::new_with_abi("sysv");
}
