struct Certificate;

impl Certificate {
    fn authorizes_signature_writeback(&self) -> bool {
        true
    }

    fn render_authorized_signature(&self) -> bool {
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

mod r2types {
    pub fn signature_writeback_decision() {}
    pub fn type_writeback_mutation_plan() {}
    pub fn type_writeback_mutation_plan_with_policy() {}
    pub fn type_writeback_authority_report_with_policy() {}
}

fn main() {
    let certificate = Certificate;
    let _ = certificate.authorizes_signature_writeback();
    let _ = certificate.render_authorized_signature();
    let _ = "signature mutation refused: stale certificate";
    r2types::signature_writeback_decision();
    r2types::type_writeback_mutation_plan();
    r2types::type_writeback_mutation_plan_with_policy();
    r2types::type_writeback_authority_report_with_policy();

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
}

mod tests {
    fn unit_tests_can_call_low_level_policy_helpers() {
        super::r2types::signature_writeback_decision();
        super::r2types::type_writeback_mutation_plan();
    }
}
