use std::fmt::Write as _;

fn render_summary(out: &mut String, selector: &str) {
    let _ = writeln!(out, "    switch ({selector}) {{");
    let _ = writeln!(out, "    case 0x1:");
    let _ = writeln!(out, "    default:");
    let _ = writeln!(out, "        break;");
    let _ = "return vm_result;";
    let _ = r2dec_ast_return();
    let _ = r2dec_ast_expr();
    let _ = writeln!(out, "    /* selector: {selector} */");
}

fn r2dec_ast_return() -> Option<()> {
    Return()
}

fn r2dec_ast_expr() -> Option<()> {
    Expr()
}

#[allow(non_snake_case)]
fn Return() -> Option<()> {
    Some(())
}

#[allow(non_snake_case)]
fn Expr() -> Option<()> {
    Some(())
}

fn main() {
    let mut out = String::new();
    render_summary(&mut out, "vm.sel");
}
