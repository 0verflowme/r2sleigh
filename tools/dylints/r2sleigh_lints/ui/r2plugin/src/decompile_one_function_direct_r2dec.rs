mod r2dec {
    pub struct DecompilerInput {
        pub prepared: bool,
    }

    pub fn lower_function_to_c(_: &DecompilerInput) -> String {
        String::new()
    }
}

fn decompile_one_function() {
    let input = r2dec::DecompilerInput { prepared: true };
    let _ = r2dec::lower_function_to_c(&input);
    let _ = input.prepared;
}

fn decompile_one_function_with_context_impl() {
    let input = r2dec::DecompilerInput { prepared: true };
    let _ = r2dec::lower_function_to_c(&input);
    let _ = input.prepared;
}

#[cfg(test)]
fn decompile_one_function_test_support() {
    let input = r2dec::DecompilerInput { prepared: true };
    let _ = r2dec::lower_function_to_c(&input);
}

fn main() {}
