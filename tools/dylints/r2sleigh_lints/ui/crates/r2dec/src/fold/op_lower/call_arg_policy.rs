struct Context;

fn is_imported_call_target(_: &str) -> bool {
    true
}

fn is_modeled_call_target(_: &str) -> bool {
    false
}

trait TraitCallArgBoundary {
    fn render_authoritative_source_call_arg(&self, func: &str) -> bool {
        is_modeled_call_target(func)
    }
}

impl TraitCallArgBoundary for Context {}

impl Context {
    fn is_imported_call_target(&self, _: &str) -> bool {
        true
    }

    fn is_modeled_call_target(&self, _: &str) -> bool {
        false
    }

    fn imported_or_modeled_call_target_for_optional_site(&self, _: Option<usize>) -> bool {
        true
    }

    fn proven_source_for_public_call_arg_call(&self) -> bool {
        true
    }

    fn call_arg_requires_result_rebuild(&self, func: &str) -> bool {
        if self.is_imported_call_target(func) {
            return false;
        }
        if self.is_modeled_call_target(func) {
            return false;
        }
        if is_imported_call_target(func) {
            return false;
        }
        false
    }

    fn choose_preferred_imported_call_arg_expr(&self) -> bool {
        self.imported_or_modeled_call_target_for_optional_site(None)
    }

    fn render_imported_call_arg(&self) -> bool {
        let _ = self.imported_or_modeled_call_target_for_optional_site(Some(0));
        self.proven_source_for_public_call_arg_call()
    }

    fn render_call_args_for_callee(&self, func: &str) -> bool {
        self.is_imported_call_target(func)
    }
}

fn main() {
    let ctx = Context;
    let _ = ctx.call_arg_requires_result_rebuild("sym.imp.atoi");
    let _ = ctx.choose_preferred_imported_call_arg_expr();
    let _ = ctx.render_imported_call_arg();
    let _ = ctx.render_call_args_for_callee("sym.imp.printf");
}
