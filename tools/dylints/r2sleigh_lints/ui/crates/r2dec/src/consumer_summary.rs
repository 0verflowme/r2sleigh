struct CFunction {
    ret_type: &'static str,
    params: Vec<&'static str>,
}

struct TypeFacts {
    register_params: Vec<&'static str>,
}

impl TypeFacts {
    fn render_authorized_signature(&self) -> Option<&'static str> {
        Some("int main(int argc)")
    }
}

fn merge_params_with_external_signature(
    params: Vec<&'static str>,
    _signature: Option<&'static str>,
) -> Vec<&'static str> {
    params
}

fn semantic_worker_summary_function(type_facts: &TypeFacts) -> CFunction {
    let trusted_signature = type_facts.render_authorized_signature();
    let mut params = merge_params_with_external_signature(Vec::new(), trusted_signature);
    if params.is_empty() {
        params.extend(type_facts.register_params.iter().copied());
    }
    CFunction {
        ret_type: trusted_signature.unwrap_or("void"),
        params,
    }
}

fn main() {
    let type_facts = TypeFacts {
        register_params: vec!["argc"],
    };
    let func = semantic_worker_summary_function(&type_facts);
    let _ = (func.ret_type, func.params);
}
