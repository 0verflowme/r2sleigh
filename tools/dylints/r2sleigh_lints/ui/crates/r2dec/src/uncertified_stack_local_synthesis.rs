struct Context;

impl Context {
    fn has_stack_slots(&self) -> bool {
        true
    }

    fn has_definitions(&self) -> bool {
        true
    }

    fn stack_synthetic_name(_offset: i64) -> String {
        "local_8".to_string()
    }

    fn resolve_stack_var(&self, offset: i64) -> Option<String> {
        if offset < 0 && (self.has_stack_slots() || self.has_definitions()) {
            return Some(Self::stack_synthetic_name(offset));
        }
        None
    }
}

fn main() {
    let _ = Context.resolve_stack_var(-8);
}
