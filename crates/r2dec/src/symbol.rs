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
///
/// Carries which table issued it. An identifier means nothing in any other
/// table, and two tables of similar size would otherwise resolve each other's
/// identifiers to real but wrong names, which is a rendering that says
/// something it does not mean.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SymbolId {
    table: TableId,
    index: u32,
}

impl SymbolId {
    /// Position in the table that issued it, for callers that index alongside.
    pub fn index(self) -> usize {
        self.index as usize
    }
}

/// Which table issued an identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TableId(u32);

impl Default for TableId {
    fn default() -> Self {
        next_table_id()
    }
}

/// Tables are numbered as they are made, so no two share a number in one run.
fn next_table_id() -> TableId {
    use std::sync::atomic::{AtomicU32, Ordering};
    static NEXT: AtomicU32 = AtomicU32::new(1);
    TableId(NEXT.fetch_add(1, Ordering::Relaxed))
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

/// Which SSA value a rendered spelling stands for.
///
/// One spelling can be reused for two SSA values, and then it names neither, so
/// the ambiguous case is recorded rather than resolved by guessing.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub enum SsaOrigin {
    /// Nothing has said which SSA value this spelling renders.
    #[default]
    Unset,
    /// This spelling renders exactly this SSA display name.
    One(Rc<str>),
    /// More than one SSA value renders as this spelling.
    Ambiguous,
}

/// One declared name.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Symbol {
    pub name: Rc<str>,
    /// The SSA display name this spelling renders, when it renders just one.
    pub ssa: SsaOrigin,
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
    /// Which table this is, so an identifier can say where it came from.
    id: TableId,
    symbols: Vec<Symbol>,
    /// Which identifiers are taken, so a second declaration cannot shadow a first.
    by_name: HashMap<String, SymbolId>,
    /// Which value each name stands for, so asking twice costs one probe, not a scan.
    by_value: HashMap<r2ssa::ValueId, SymbolId>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            id: next_table_id(),
            ..Default::default()
        }
    }

    /// Mint an identifier for a position in this table.
    fn id_at(&self, index: usize) -> SymbolId {
        SymbolId {
            table: self.id,
            index: index as u32,
        }
    }

    /// Resolve an identifier this table issued, refusing one it did not.
    fn resolve(&self, id: SymbolId) -> usize {
        assert!(
            id.table == self.id,
            "identifier from table {:?} read in table {:?}: an identifier only \
             names something in the table that issued it",
            id.table,
            self.id
        );
        id.index()
    }

    /// Declare a name, returning the identifier that refers to it.
    ///
    /// A requested name already in use is given a numbered suffix rather than
    /// being merged, because two distinct values sharing one identifier is how a
    /// rendering says something it does not mean.
    #[track_caller]
    pub fn declare(
        &mut self,
        name: impl Into<String>,
        ty: CType,
        role: SymbolRole,
        origin: SymbolOrigin,
    ) -> SymbolId {
        let requested = name.into();
        if let Ok(want) = std::env::var("R2SLEIGH_TRACE_NAME")
            && requested.eq_ignore_ascii_case(&want)
        {
            eprintln!(
                "NAMEDECLARE {requested} via {}",
                std::panic::Location::caller()
            );
        }
        let name: Rc<str> = Rc::from(self.unique_name(requested));
        let id = self.id_at(self.symbols.len());
        self.by_name.insert(name.to_string(), id);
        if let Some(value) = origin.value {
            self.by_value.entry(value).or_insert(id);
        }
        self.symbols.push(Symbol {
            name,
            ssa: SsaOrigin::Unset,
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
    /// The SSA display name this identifier renders, when it renders just one.
    ///
    /// A rendered spelling and an SSA display name are different strings for the
    /// same value, so a side table keyed by the latter must be asked with this.
    pub fn ssa_name(&self, id: SymbolId) -> Option<Rc<str>> {
        match &self.get(id).ssa {
            SsaOrigin::One(name) => Some(Rc::clone(name)),
            SsaOrigin::Unset | SsaOrigin::Ambiguous => None,
        }
    }

    /// Record which SSA value this identifier was minted to render.
    pub fn note_ssa_name(&mut self, id: SymbolId, ssa_name: &str) {
        let index = self.resolve(id);
        let slot = &mut self.symbols[index].ssa;
        *slot = match slot {
            SsaOrigin::Unset => SsaOrigin::One(Rc::from(ssa_name)),
            SsaOrigin::One(current) if &**current == ssa_name => return,
            SsaOrigin::One(_) | SsaOrigin::Ambiguous => SsaOrigin::Ambiguous,
        };
    }

    #[track_caller]
    pub fn declare_or_reuse(&mut self, name: &str) -> SymbolId {
        // Which site puts a given spelling on the page. Every identifier is
        // minted here, so a name reaching the output with nothing defining it
        // was made by exactly one caller and this says which. Reading the
        // resolvers found four that could have produced `rcx_4` and none that
        // did, which is how long guessing takes.
        if let Ok(want) = std::env::var("R2SLEIGH_TRACE_NAME")
            && name.eq_ignore_ascii_case(&want)
        {
            eprintln!("NAMEMINT {name} via {}", std::panic::Location::caller());
        }
        // Mark, do not read. Six attempts reasoned about which resolver ought to
        // have produced a name; spelling the mint site into the name says which
        // one did, because only the spelling that reaches the page survives.
        let marked;
        let name = match std::env::var("R2SLEIGH_TRACE_NAME") {
            Ok(want) if name.eq_ignore_ascii_case(&want) => {
                marked = format!("{name}__L{}", std::panic::Location::caller().line());
                marked.as_str()
            }
            _ => name,
        };
        if let Some(existing) = self.by_name.get(name) {
            return *existing;
        }
        // A rendered identifier is spelled by `spell_var`, which never emits a
        // raw SSA name. One that arrives here still wearing its space prefix came
        // from somewhere that handed a machine name straight to the table, and
        // that is how `tmp:25400` reaches the page as `tmp_25400`.
        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() && name.contains(':') {
            eprintln!("RAWMINT name={name}");
        }
        let id = self.id_at(self.symbols.len());
        self.by_name.insert(name.to_string(), id);
        self.symbols.push(Symbol {
            name: Rc::from(name),
            ssa: SsaOrigin::Unset,
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
            if let Ok(want) = std::env::var("R2SLEIGH_TRACE_NAME")
                && target.eq_ignore_ascii_case(&want)
            {
                eprintln!(
                    "NAMEFOLLOW {} -> {target}",
                    self.symbols[index].name
                );
            }
            let previous =
                std::mem::replace(&mut self.symbols[index].name, Rc::from(target.as_str()));
            self.by_name.remove(&*previous);
            self.by_name.insert(target.clone(), self.id_at(index));
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
        &self.symbols[self.resolve(id)]
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
        &self.symbols[self.resolve(id)].name
    }

    pub fn ty(&self, id: SymbolId) -> &CType {
        &self.symbols[self.resolve(id)].ty
    }

    /// Change what a name reads as, keeping every reference to it intact.
    ///
    /// Renaming used to mean rewriting matching words across the whole rendered
    /// function and hoping declarations and uses stayed in step. A reference is
    /// an identifier rather than a spelling, so there is nothing to keep in step.
    #[track_caller]
    pub fn rename(&mut self, id: SymbolId, name: impl Into<String>) {
        let requested = name.into();
        if let Ok(want) = std::env::var("R2SLEIGH_TRACE_NAME")
            && requested.eq_ignore_ascii_case(&want)
        {
            eprintln!(
                "NAMERENAME {} -> {requested} via {}",
                self.name(id),
                std::panic::Location::caller()
            );
        }
        let index = self.resolve(id);
        if *self.symbols[index].name == *requested {
            return;
        }
        let name = self.unique_name(requested);
        let previous =
            std::mem::replace(&mut self.symbols[index].name, Rc::from(name.as_str()));
        self.by_name.remove(&*previous);
        self.by_name.insert(name, id);
    }

    pub fn set_type(&mut self, id: SymbolId, ty: CType) {
        let index = self.resolve(id);
        self.symbols[index].ty = ty;
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
            .map(|(index, symbol)| (self.id_at(index), symbol))
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
#[track_caller]
#[inline(always)]
pub fn var_ref(symbols: &RefCell<SymbolTable>, name: impl AsRef<str>) -> CExpr {
    CExpr::Var(crate::symbol::declare(&symbols, name.as_ref()))
}

/// Declare this spelling, or return the identifier it already has.
///
/// The borrow ends when this returns, so two declarations may appear in one
/// statement. Writing `borrow_mut()` inline holds the guard to the end of the
/// statement instead, and a second declaration there deadlocks.
#[track_caller]
#[inline(always)]
pub fn declare(symbols: &RefCell<SymbolTable>, name: impl AsRef<str>) -> SymbolId {
    let name = name.as_ref();
    if let Ok(want) = std::env::var("R2SLEIGH_TRACE_NAME")
        && name.eq_ignore_ascii_case(&want)
    {
        eprintln!("NAMEDECL {name} via {}", std::panic::Location::caller());
    }
    symbols.borrow_mut().declare_or_reuse(name)
}

/// How a reference is spelled, for code that holds the table rather than a self.
pub fn spelling(symbols: &RefCell<SymbolTable>, id: SymbolId) -> Rc<str> {
    symbols.borrow().spelling(id)
}
