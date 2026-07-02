#[derive(Default)]
struct FunctionFacts {
    types: usize,
    summary_view: usize,
    assumption_usage: usize,
}

#[derive(Default)]
struct DecompilerContext {
    function_facts: FunctionFacts,
}

fn bad_direct_function_facts_writes(mut function_facts: FunctionFacts) {
    function_facts.types = 1;
    function_facts.summary_view = 2;
    function_facts.assumption_usage = 3;
}

fn bad_nested_function_facts_write(mut context: DecompilerContext) {
    context.function_facts.types = 4;
}

fn main() {}
