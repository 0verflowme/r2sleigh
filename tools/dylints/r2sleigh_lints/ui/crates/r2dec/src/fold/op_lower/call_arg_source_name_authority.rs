struct Binding {
    source_var_name: Option<String>,
    source_value_id: Option<u64>,
    source_call: Option<(u64, usize)>,
}

struct Context;

fn wrapper<T>(value: T) -> T {
    value
}

impl Context {
    fn source_var_name_has_prepared_call_arg_authority(&self, _: &str) -> bool {
        true
    }

    fn certified_call_args_for_site_with_direct_target(&self, binding: &Binding) -> bool {
        binding.source_value_id.is_some()
            || binding.source_call.is_some()
            || binding.source_var_name.is_some()
    }

    fn certified_call_args_for_site(&self, binding: &Binding) -> bool {
        (binding.source_value_id.is_none()
            && binding.source_var_name.is_none()
            && binding.source_call.is_none())
            || binding
                .source_var_name
                .as_ref()
                .is_some_and(|name| !name.is_empty())
            || binding.source_var_name.as_ref().is_some()
            || Some(&binding.source_var_name).is_some()
            || (&binding.source_var_name).is_some()
            || wrapper(binding.source_var_name.as_ref()).is_some()
            || (&wrapper(binding.source_var_name.as_ref())).is_some()
            || (!binding.source_var_name.is_none())
            || (binding.source_var_name.as_deref() as Option<&str>).is_some()
            || { binding.source_var_name.as_ref() }.is_some()
    }

    fn call_arg_binding_has_render_authority(&self, binding: &Binding) -> bool {
        binding.source_value_id.is_some()
            || binding.source_call.is_some()
            || binding
                .source_var_name
                .as_deref()
                .is_some_and(|name| self.source_var_name_has_prepared_call_arg_authority(name))
    }

    fn recover_call_arg_expr_from_source_var(&self, binding: &Binding) -> Option<String> {
        binding.source_var_name.clone()
    }

    fn ordinary_source_name_check(&self, binding: &Binding) -> bool {
        binding.source_var_name.is_some()
    }
}

fn main() {
    let ctx = Context;
    let binding = Binding {
        source_var_name: Some("x0_1".to_string()),
        source_value_id: None,
        source_call: None,
    };
    let _ = ctx.certified_call_args_for_site_with_direct_target(&binding);
    let _ = ctx.certified_call_args_for_site(&binding);
    let _ = ctx.call_arg_binding_has_render_authority(&binding);
    let _ = ctx.recover_call_arg_expr_from_source_var(&binding);
    let _ = ctx.ordinary_source_name_check(&binding);
}
