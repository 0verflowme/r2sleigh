struct RenderFacts;

impl RenderFacts {
    fn member_access_for_op_any_direction(&self) -> Option<()> {
        Some(())
    }

    fn array_access_for_op_any_direction(&self) -> Option<()> {
        Some(())
    }
}

struct Context {
    render_facts: RenderFacts,
}

impl Context {
    fn certified_field_name_for_offset(&self) -> Option<()> {
        self.render_facts.member_access_for_op_any_direction()
    }

    fn certified_array_access_for_current_op(&self) -> Option<()> {
        self.render_facts.array_access_for_op_any_direction()
    }
}

fn main() {
    let ctx = Context {
        render_facts: RenderFacts,
    };
    let _ = ctx.certified_field_name_for_offset();
    let _ = ctx.certified_array_access_for_current_op();
}
