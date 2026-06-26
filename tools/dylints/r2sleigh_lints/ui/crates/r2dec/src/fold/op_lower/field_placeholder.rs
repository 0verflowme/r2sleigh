struct Context;

impl Context {
    fn fallback_aggregate_field_name(type_name: &str, offset: u64) -> Option<String> {
        (!type_name.trim().is_empty()).then(|| format!("f_{offset:x}"))
    }

    fn typedef_name_looks_aggregate(&self, type_name: &str) -> bool {
        let trimmed = type_name.trim();
        trimmed
            .chars()
            .next()
            .is_some_and(|ch| ch.is_ascii_uppercase())
    }
}

fn main() {
    let ctx = Context;
    let _ = Context::fallback_aggregate_field_name("Demo", 0x30);
    let _ = ctx.typedef_name_looks_aggregate("Demo");
}
