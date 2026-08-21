//! The names a rendered function is allowed to use.
//!
//! An identifier in the output either names something the function declares or
//! names something outside it. Nothing else is a name, and the renderer used to
//! have no way to say so: every identifier was a `String`, so a machine register
//! that escaped the fold looked exactly like a local, and the only way to notice
//! was to scan the finished text for words that resolved to nothing. That scan
//! could be satisfied by declaring the word, which is what happened.
//!
//! A symbol table removes the choice. A local exists because it was declared,
//! and declaring it is what returns the identifier that can refer to it, so an
//! undeclared local cannot be written down. A name from outside carries what
//! kind of outside thing it is, so calling something external is a claim a
//! reader can check rather than a string that arrived from somewhere.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use serde::{Deserialize, Serialize};

use crate::ast::{CExpr, CType};

/// A name the function declares. Minted only by declaring one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SymbolId(u32);

impl SymbolId {
    /// Position in the table that issued it, for callers that index alongside.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// What a declared name stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolRole {
    /// An incoming argument at this parameter position.
    Parameter(u32),
    /// A frame slot at this offset from the frame base.
    StackLocal(i64),
    /// A value the function computes and more than one place reads.
    Carrier,
}

/// Where a declared name came from, so a rendered name can be traced back.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct SymbolOrigin {
    /// The canonical value this name stands for, when one value defines it.
    pub value: Option<r2ssa::ValueId>,
}

/// One declared name.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Symbol {
    pub name: Rc<str>,
    pub ty: CType,
    pub role: SymbolRole,
    pub origin: SymbolOrigin,
}

/// Why a name that the function does not declare is allowed to appear.
///
/// Each variant is a claim about something outside the function, and a claim is
/// reviewable in a way that an arbitrary string is not. There is deliberately no
/// variant meaning "a name that arrived from the machine", because that is the
/// case this type exists to make unwritable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExternalKind {
    /// Another function in the binary.
    Function,
    /// A symbol resolved through the import table.
    Import,
    /// A named object outside any frame.
    Global,
    /// An operation the target defines that C has no operator for.
    Intrinsic,
}

impl std::fmt::Display for ExternalKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Function => "function",
            Self::Import => "import",
            Self::Global => "global",
            Self::Intrinsic => "intrinsic",
        })
    }
}

/// Every name one rendered function declares.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct SymbolTable {
    symbols: Vec<Symbol>,
    /// Which identifiers are taken, so a second declaration cannot shadow a first.
    by_name: HashMap<String, SymbolId>,
    /// Which value each name stands for, so asking twice costs one probe, not a scan.
    by_value: HashMap<r2ssa::ValueId, SymbolId>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Declare a name, returning the identifier that refers to it.
    ///
    /// A requested name already in use is given a numbered suffix rather than
    /// being merged, because two distinct values sharing one identifier is how a
    /// rendering says something it does not mean.
    pub fn declare(
        &mut self,
        name: impl Into<String>,
        ty: CType,
        role: SymbolRole,
        origin: SymbolOrigin,
    ) -> SymbolId {
        let requested = name.into();
        let name: Rc<str> = Rc::from(self.unique_name(requested));
        let id = SymbolId(self.symbols.len() as u32);
        self.by_name.insert(name.to_string(), id);
        if let Some(value) = origin.value {
            self.by_value.entry(value).or_insert(id);
        }
        self.symbols.push(Symbol {
            name,
            ty,
            role,
            origin,
        });
        id
    }

    /// Declare a name for a value, or return the one that value already has.
    pub fn declare_value(
        &mut self,
        value: r2ssa::ValueId,
        name: impl Into<String>,
        ty: CType,
        role: SymbolRole,
    ) -> SymbolId {
        if let Some(existing) = self.for_value(value) {
            return existing;
        }
        self.declare(
            name,
            ty,
            role,
            SymbolOrigin {
                value: Some(value),
            },
        )
    }

    /// The identifier for this spelling, declaring it if nothing has yet.
    ///
    /// Expression building asks for a name many times over as it walks a value,
    /// and every ask means the same variable. Minting a second identifier for the
    /// second ask would put two variables on the page for one value, so the
    /// spelling is what decides identity here.
    pub fn declare_or_reuse(&mut self, name: &str) -> SymbolId {
        if let Some(existing) = self.by_name.get(name) {
            return *existing;
        }
        let id = SymbolId(self.symbols.len() as u32);
        self.by_name.insert(name.to_string(), id);
        self.symbols.push(Symbol {
            name: Rc::from(name),
            ty: CType::Unknown,
            role: SymbolRole::Carrier,
            origin: SymbolOrigin::default(),
        });
        id
    }

    /// Apply a rename the caller worked out, keeping every reference intact.
    ///
    /// A reference is an identifier, so moving a spelling moves every mention of
    /// it at once. Nothing walks the body to keep declarations and uses in step,
    /// because they were never separately spelled.
    pub fn follow_renames(&mut self, renames: &HashMap<String, String>) {
        if renames.is_empty() {
            return;
        }
        for index in 0..self.symbols.len() {
            let Some(target) = renames.get(&*self.symbols[index].name) else {
                continue;
            };
            if self.by_name.contains_key(target) {
                // Two names cannot become one, or two variables would.
                continue;
            }
            let previous =
                std::mem::replace(&mut self.symbols[index].name, Rc::from(target.as_str()));
            self.by_name.remove(&*previous);
            self.by_name.insert(target.clone(), SymbolId(index as u32));
        }
    }

    /// An identifier that no declaration has taken yet.
    fn unique_name(&self, requested: String) -> String {
        if !self.by_name.contains_key(&requested) {
            return requested;
        }
        // Start past the collision rather than at zero, so n declarations of one
        // name cost n probes in total rather than n squared.
        let mut suffix = 2usize;
        loop {
            let candidate = format!("{requested}_{suffix}");
            if !self.by_name.contains_key(&candidate) {
                return candidate;
            }
            suffix += 1;
        }
    }

    pub fn get(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id.index()]
    }

    /// The spelling as a shared handle, so a caller can drop the table borrow.
    ///
    /// Reading a spelling and then building an expression is the common shape,
    /// and building mints, so a caller holding a borrow across it would panic.
    /// Cloning the handle is a refcount bump, not a copy of the text.
    pub fn spelling(&self, id: SymbolId) -> Rc<str> {
        Rc::clone(&self.get(id).name)
    }

    pub fn name(&self, id: SymbolId) -> &str {
        &self.symbols[id.index()].name
    }

    pub fn ty(&self, id: SymbolId) -> &CType {
        &self.symbols[id.index()].ty
    }

    /// Change what a name reads as, keeping every reference to it intact.
    ///
    /// Renaming used to mean rewriting matching words across the whole rendered
    /// function and hoping declarations and uses stayed in step. A reference is
    /// an identifier rather than a spelling, so there is nothing to keep in step.
    pub fn rename(&mut self, id: SymbolId, name: impl Into<String>) {
        let requested = name.into();
        if *self.symbols[id.index()].name == *requested {
            return;
        }
        let name = self.unique_name(requested);
        let previous =
            std::mem::replace(&mut self.symbols[id.index()].name, Rc::from(name.as_str()));
        self.by_name.remove(&*previous);
        self.by_name.insert(name, id);
    }

    pub fn set_type(&mut self, id: SymbolId, ty: CType) {
        self.symbols[id.index()].ty = ty;
    }

    /// The identifier standing for a canonical value, if one was declared for it.
    pub fn for_value(&self, value: r2ssa::ValueId) -> Option<SymbolId> {
        self.by_value.get(&value).copied()
    }

    /// The identifier spelled this way, if any declaration took that spelling.
    pub fn by_name(&self, name: &str) -> Option<SymbolId> {
        self.by_name.get(name).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (SymbolId, &Symbol)> {
        self.symbols
            .iter()
            .enumerate()
            .map(|(index, symbol)| (SymbolId(index as u32), symbol))
    }

    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table() -> SymbolTable {
        SymbolTable::new()
    }

    #[test]
    fn declaring_is_what_produces_a_reference() {
        let mut symbols = table();
        let id = symbols.declare(
            "total",
            CType::Int(32),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );

        assert_eq!(symbols.name(id), "total");
        assert_eq!(symbols.by_name("total"), Some(id));
        // Nothing declared it, so nothing refers to it.
        assert_eq!(symbols.by_name("eax"), None);
    }

    #[test]
    fn two_declarations_never_share_one_identifier() {
        let mut symbols = table();
        let first = symbols.declare(
            "h",
            CType::Int(32),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );
        let second = symbols.declare(
            "h",
            CType::Int(64),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );

        assert_ne!(first, second);
        assert_eq!(symbols.name(first), "h");
        assert_eq!(symbols.name(second), "h_2");
    }

    #[test]
    fn one_value_gets_one_name_however_often_it_is_asked_for() {
        let mut symbols = table();
        let value = r2ssa::ValueId(7);
        let first = symbols.declare_value(value, "h", CType::Int(32), SymbolRole::Carrier);
        let again = symbols.declare_value(value, "other", CType::Int(32), SymbolRole::Carrier);

        assert_eq!(first, again);
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols.for_value(value), Some(first));
    }

    #[test]
    fn renaming_moves_the_spelling_and_leaves_the_reference_alone() {
        let mut symbols = table();
        let id = symbols.declare(
            "x0_2",
            CType::Int(64),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );

        symbols.rename(id, "hash");

        assert_eq!(symbols.name(id), "hash");
        assert_eq!(symbols.by_name("hash"), Some(id));
        assert_eq!(symbols.by_name("x0_2"), None);
    }

    #[test]
    fn renaming_onto_a_taken_spelling_does_not_merge_two_symbols() {
        let mut symbols = table();
        let taken = symbols.declare(
            "hash",
            CType::Int(32),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );
        let other = symbols.declare(
            "x0_2",
            CType::Int(64),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );

        symbols.rename(other, "hash");

        assert_eq!(symbols.name(taken), "hash");
        assert_eq!(symbols.name(other), "hash_2");
        assert_eq!(symbols.by_name("hash"), Some(taken));
    }
}

#[cfg(test)]
mod reuse_tests {
    use super::*;

    #[test]
    fn asking_twice_for_one_spelling_yields_one_variable() {
        let mut symbols = SymbolTable::new();
        let first = symbols.declare_or_reuse("rax");
        let again = symbols.declare_or_reuse("rax");

        assert_eq!(first, again, "one spelling is one variable while folding");
        assert_eq!(symbols.len(), 1);
    }

    #[test]
    fn two_spellings_stay_two_variables() {
        let mut symbols = SymbolTable::new();
        let rax = symbols.declare_or_reuse("rax");
        let rcx = symbols.declare_or_reuse("rcx");

        assert_ne!(rax, rcx);
        assert_eq!(symbols.name(rax), "rax");
        assert_eq!(symbols.name(rcx), "rcx");
    }

    #[test]
    fn a_declared_name_is_not_reissued_by_reuse() {
        // declare() is what mints a distinct variable; reuse must respect it.
        let mut symbols = SymbolTable::new();
        let declared = symbols.declare(
            "total",
            CType::Int(32),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );

        assert_eq!(symbols.declare_or_reuse("total"), declared);
        assert_eq!(symbols.len(), 1);
    }
}

/// A reference to this spelling, declaring it if nothing has yet.
///
/// Analysis builds candidate expressions before anything decides to render
/// them, so it mints here rather than handing spellings forward for a later
/// layer to declare. A candidate that is dropped costs one unused table entry.
pub fn var_ref(symbols: &RefCell<SymbolTable>, name: impl AsRef<str>) -> CExpr {
    CExpr::Var(symbols.borrow_mut().declare_or_reuse(name.as_ref()))
}

/// How a reference is spelled, for code that holds the table rather than a self.
pub fn spelling(symbols: &RefCell<SymbolTable>, id: SymbolId) -> Rc<str> {
    symbols.borrow().spelling(id)
}
