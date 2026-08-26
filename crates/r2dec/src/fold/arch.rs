/// The condition codes of the x86 register file, for fixtures that state a target.
///
/// Production derives this from the machine context rather than listing it, and
/// this list exists only so a test fixture can say which target it is about.
#[cfg(test)]
pub(crate) const X86_FLAG_REGISTERS: &[&str] = &[
    "ac", "af", "c0", "c1", "c2", "c3", "cf", "df", "id", "if", "iopl", "nt", "of", "pf", "rf",
    "sf", "tf", "vif", "vip", "vm", "zf",
];
