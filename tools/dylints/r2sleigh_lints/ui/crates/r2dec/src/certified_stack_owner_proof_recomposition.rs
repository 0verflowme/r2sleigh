struct FunctionRenderFacts;

impl FunctionRenderFacts {
    fn has_stack_slot_offset(&self, _offset: i64) -> bool {
        true
    }
}

struct Context {
    render_facts: FunctionRenderFacts,
}

impl Context {
    fn preferred_stack_alias_name(&self, _name: &str) -> Option<String> {
        Some("local_8".to_string())
    }

    fn stack_slot_provenance_for_name(&self, _name: &str) -> Option<i64> {
        Some(-8)
    }

    fn visible_binding_matches_stack_owner(&self, _name: &str, _offset: i64) -> bool {
        true
    }

    fn typed_stack_owner_matches(&self, _name: &str, _offset: i64) -> bool {
        true
    }

    fn certified_stack_owner_authorized(&self, name: &str, offset: i64) -> bool {
        self.render_facts.has_stack_slot_offset(offset)
            && self.visible_binding_matches_stack_owner(name, offset)
            && self.typed_stack_owner_matches(name, offset)
    }

    fn certified_call_result_owner_name_for_stack_alias(&self, name: &str) -> Option<String> {
        self.preferred_stack_alias_name(name)
    }

    fn certified_call_result_source_for_stack_owner_alias(&self, name: &str) -> Option<i64> {
        self.stack_slot_provenance_for_name(name)
    }

    fn certified_stack_owner_authorized_by_function_facts(
        &self,
        function_facts: &FunctionFacts,
        name: &str,
        offset: i64,
    ) -> bool {
        function_facts.function_facts_stack_owner_is_exact(name, offset)
            && self.render_facts.has_stack_slot_offset(offset)
    }

    fn certified_call_result_owner_name_authorized_by_function_facts(
        &self,
        function_facts: &FunctionFacts,
        name: &str,
    ) -> Option<String> {
        function_facts
            .stack_owner_authorizes_call_result_name(name)
            .then(|| self.preferred_stack_alias_name(name))
            .flatten()
    }
}

struct FunctionFacts;

impl FunctionFacts {
    fn function_facts_stack_owner_is_exact(&self, _name: &str, _offset: i64) -> bool {
        true
    }

    fn stack_owner_authorizes_call_result_name(&self, _name: &str) -> bool {
        true
    }
}

fn main() {
    let ctx = Context {
        render_facts: FunctionRenderFacts,
    };
    let _ = ctx.certified_stack_owner_authorized("local_8", -8);
    let _ = ctx.certified_call_result_owner_name_for_stack_alias("local_8");
    let _ = ctx.certified_call_result_source_for_stack_owner_alias("local_8");
    let _ =
        ctx.certified_stack_owner_authorized_by_function_facts(&FunctionFacts, "local_8", -8);
    let _ =
        ctx.certified_call_result_owner_name_authorized_by_function_facts(&FunctionFacts, "local_8");
}
