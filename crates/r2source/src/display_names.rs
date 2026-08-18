//! Names radare2 already holds for the addresses a function touches.
//!
//! A name says how to spell something, not what it does. Semantic
//! classification, route selection and type inference deliberately work
//! without them, because a call to `sym.imp.strlen` has to be recognised from
//! its callsite and its effects rather than from the seven letters after the
//! dot. Keeping the names in a carrier of their own is what makes that
//! separation checkable: nothing outside rendering has a reason to read this
//! type, and the repo lint says so.
//!
//! What it is for is the other half of the job. When the renderer has proven
//! what a call does, it still has to print something, and `sub_100002afc` is a
//! worse spelling of the same fact than `sym.imp.strcmp`.

use std::collections::BTreeMap;

/// Display-only names, keyed by the address they belong to.
///
/// Ordered maps, because the rendered output is compared byte for byte and two
/// runs over the same binary have to agree.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DisplayNames {
    functions: BTreeMap<u64, String>,
    symbols: BTreeMap<u64, String>,
    strings: BTreeMap<u64, String>,
    /// The function's own parameters, in order.
    ///
    /// Positional rather than address-keyed, because a parameter is identified
    /// by where it sits in the signature and not by a place in memory. Still a
    /// spelling and nothing more: it does not say what the parameter is for.
    parameters: Vec<String>,
}

impl DisplayNames {
    pub fn new() -> Self {
        Self::default()
    }

    /// True when there is nothing to say about anything.
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
            && self.symbols.is_empty()
            && self.strings.is_empty()
            && self.parameters.is_empty()
    }

    /// Record the name of a function that starts at `addr`.
    ///
    /// An empty name is not a name, and recording one would let a caller
    /// replace a usable spelling with nothing.
    pub fn insert_function(&mut self, addr: u64, name: impl Into<String>) {
        insert_named(&mut self.functions, addr, name.into());
    }

    /// Record the name of a symbol at `addr`, such as an import stub.
    pub fn insert_symbol(&mut self, addr: u64, name: impl Into<String>) {
        insert_named(&mut self.symbols, addr, name.into());
    }

    /// Record the string literal stored at `addr`.
    pub fn insert_string(&mut self, addr: u64, value: impl Into<String>) {
        insert_named(&mut self.strings, addr, value.into());
    }

    /// Record the function's parameter names, in signature order.
    ///
    /// A generic placeholder is not a name: recording `arg0` would displace the
    /// renderer's own fallback with something no more informative, and would
    /// hide that the source never said.
    pub fn set_parameters<I, S>(&mut self, names: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.parameters = names
            .into_iter()
            .map(Into::into)
            .map(|name| {
                if is_placeholder_parameter_name(&name) {
                    String::new()
                } else {
                    name
                }
            })
            .collect();
        while matches!(self.parameters.last(), Some(name) if name.is_empty()) {
            self.parameters.pop();
        }
    }

    /// The name the source gave parameter `index`, if it gave one.
    pub fn parameter(&self, index: usize) -> Option<&str> {
        self.parameters
            .get(index)
            .map(String::as_str)
            .filter(|name| !name.is_empty())
    }

    pub fn parameters(&self) -> &[String] {
        &self.parameters
    }

    pub fn functions(&self) -> &BTreeMap<u64, String> {
        &self.functions
    }

    pub fn symbols(&self) -> &BTreeMap<u64, String> {
        &self.symbols
    }

    pub fn strings(&self) -> &BTreeMap<u64, String> {
        &self.strings
    }

    /// The best spelling for `addr`, preferring a function over a symbol.
    ///
    /// A function name is the more specific fact: an address can carry both
    /// when radare2 has recovered a function over an import stub.
    pub fn name_for(&self, addr: u64) -> Option<&str> {
        self.functions
            .get(&addr)
            .or_else(|| self.symbols.get(&addr))
            .map(String::as_str)
    }

    /// Take every name from `other` that this carrier does not already hold.
    ///
    /// Existing entries win, so a caller that has already recorded a more
    /// specific name cannot have it replaced by a later, vaguer one.
    pub fn absorb(&mut self, other: &Self) {
        for (addr, name) in &other.functions {
            self.functions.entry(*addr).or_insert_with(|| name.clone());
        }
        for (addr, name) in &other.symbols {
            self.symbols.entry(*addr).or_insert_with(|| name.clone());
        }
        for (addr, value) in &other.strings {
            self.strings.entry(*addr).or_insert_with(|| value.clone());
        }
        if self.parameters.is_empty() {
            self.parameters = other.parameters.clone();
        }
    }
}

/// Whether a name is one of the placeholders a tool invents when it has none.
fn is_placeholder_parameter_name(name: &str) -> bool {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return true;
    }
    for prefix in ["arg", "param", "a", "p"] {
        if let Some(rest) = trimmed.strip_prefix(prefix)
            && !rest.is_empty()
            && rest.bytes().all(|byte| byte.is_ascii_digit())
        {
            return true;
        }
    }
    false
}

fn insert_named(map: &mut BTreeMap<u64, String>, addr: u64, name: String) {
    if name.is_empty() {
        return;
    }
    map.insert(addr, name);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_function_name_is_preferred_over_a_symbol_at_the_same_address() {
        let mut names = DisplayNames::new();
        names.insert_symbol(0x1000, "sym.imp.strlen");
        names.insert_function(0x1000, "dbg.strlen");
        assert_eq!(names.name_for(0x1000), Some("dbg.strlen"));
    }

    #[test]
    fn a_symbol_answers_when_no_function_covers_the_address() {
        let mut names = DisplayNames::new();
        names.insert_symbol(0x2000, "sym.imp.strcmp");
        assert_eq!(names.name_for(0x2000), Some("sym.imp.strcmp"));
        assert_eq!(names.name_for(0x2001), None);
    }

    /// An empty spelling is not an improvement on having no name, and storing
    /// it would let a later caller erase a usable one.
    #[test]
    fn an_empty_name_is_not_recorded() {
        let mut names = DisplayNames::new();
        names.insert_function(0x3000, "");
        names.insert_symbol(0x3000, "");
        names.insert_string(0x3000, "");
        assert!(names.is_empty());
    }

    /// `arg0` is what the renderer already falls back to, so recording it as
    /// though the source had said it would hide that the source said nothing.
    #[test]
    fn a_placeholder_parameter_name_is_not_recorded() {
        let mut names = DisplayNames::new();
        names.set_parameters(["password", "arg1", "", "len"]);
        assert_eq!(names.parameter(0), Some("password"));
        assert_eq!(names.parameter(1), None);
        assert_eq!(names.parameter(2), None);
        assert_eq!(names.parameter(3), Some("len"));
        assert_eq!(names.parameter(4), None);
    }

    /// Trailing placeholders carry nothing, so the list stops at the last name
    /// the source actually gave.
    #[test]
    fn trailing_placeholders_are_dropped() {
        let mut names = DisplayNames::new();
        names.set_parameters(["msg", "arg1", "arg2"]);
        assert_eq!(names.parameters().len(), 1);
    }

    #[test]
    fn absorbing_keeps_the_name_already_held() {
        let mut names = DisplayNames::new();
        names.insert_function(0x4000, "dbg.original");
        let mut other = DisplayNames::new();
        other.insert_function(0x4000, "sub_4000");
        other.insert_symbol(0x4008, "sym.imp.memcpy");
        names.absorb(&other);
        assert_eq!(names.name_for(0x4000), Some("dbg.original"));
        assert_eq!(names.name_for(0x4008), Some("sym.imp.memcpy"));
    }
}
