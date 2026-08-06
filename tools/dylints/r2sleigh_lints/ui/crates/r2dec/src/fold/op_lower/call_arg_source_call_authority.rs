struct Binding {
    source_call: Option<(u64, usize)>,
    source_value_id: Option<u64>,
}

struct Context;

fn wrapper<T>(value: T) -> T {
    value
}

impl Context {
    fn certified_call_args_for_site_with_direct_target(&self, binding: &Binding) -> bool {
        binding.source_value_id.is_some() || binding.source_call.is_some()
    }

    fn certified_call_args_for_site(&self, binding: &Binding) -> bool {
        binding.source_call.is_none()
            || Some(&binding.source_call).is_some()
            || (&binding.source_call).is_some()
            || wrapper(binding.source_call.as_ref()).is_some()
    }

    fn call_arg_binding_has_render_authority(&self, binding: &Binding) -> bool {
        binding.source_call.is_some()
    }

    fn ordinary_source_call_check(&self, binding: &Binding) -> bool {
        binding.source_call.is_some()
    }
}

fn main() {
    let ctx = Context;
    let binding = Binding {
        source_call: Some((0x1000, 0)),
        source_value_id: None,
    };
    let _ = ctx.certified_call_args_for_site_with_direct_target(&binding);
    let _ = ctx.certified_call_args_for_site(&binding);
    let _ = ctx.call_arg_binding_has_render_authority(&binding);
    let _ = ctx.ordinary_source_call_check(&binding);
}
