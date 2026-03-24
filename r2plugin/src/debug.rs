use std::fmt;

pub(crate) fn trace(args: fmt::Arguments<'_>) {
    if std::env::var_os("R2SLEIGH_TRACE").is_none() {
        return;
    }
    eprintln!("r2sleigh[rust] {args}");
}
