struct Context;

impl Context {
    fn fallback_owned_call_result_stack_local_name_for_source(&self) -> Option<String> {
        Some("buf".to_string())
    }

    fn derive_stable_owned_call_result_name_for_alias(&self, alias: &str) -> Option<String> {
        let fallback_stack_local = self.semantic_stack_owner_name_for_alias(alias);
        fallback_stack_local
    }

    fn semantic_stack_owner_name_for_alias(&self, alias: &str) -> Option<String> {
        Some(alias.to_string())
    }
}

fn main() {
    let ctx = Context;
    let _ = ctx.derive_stable_owned_call_result_name_for_alias("rax_1");
}
