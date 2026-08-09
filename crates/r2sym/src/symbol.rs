use r2ssa::FunctionSemanticLinkage;
use std::collections::{BTreeMap, HashMap};

/// One immutable, explicitly linked symbol supplied with a symbolic scope.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionSymbol {
    pub addr: u64,
    pub name: String,
    pub linkage: FunctionSemanticLinkage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionSymbolSnapshotError {
    EmptyName,
    NameContainsNul,
    ConflictingDuplicate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionSymbolEvidenceProvenance {
    RequestLocalAnalysis,
}

/// Canonically ordered, untrusted per-request analysis evidence. Name-backed
/// symbolic contracts are exposed only for entries explicitly marked Imported,
/// but this snapshot is never source lineage or final CertifiedC authority.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionSymbolSnapshot {
    symbols: BTreeMap<u64, FunctionSymbol>,
    imported_names: HashMap<u64, String>,
}

impl FunctionSymbolSnapshot {
    pub fn try_from_symbols(
        symbols: impl IntoIterator<Item = FunctionSymbol>,
    ) -> Result<Self, FunctionSymbolSnapshotError> {
        let mut canonical = BTreeMap::new();
        for symbol in symbols {
            if symbol.name.is_empty() {
                return Err(FunctionSymbolSnapshotError::EmptyName);
            }
            if symbol.name.contains('\0') {
                return Err(FunctionSymbolSnapshotError::NameContainsNul);
            }
            if let Some(previous) = canonical.get(&symbol.addr) {
                if previous != &symbol {
                    return Err(FunctionSymbolSnapshotError::ConflictingDuplicate);
                }
                continue;
            }
            canonical.insert(symbol.addr, symbol);
        }
        let imported_names = canonical
            .iter()
            .filter(|(_, symbol)| symbol.linkage == FunctionSemanticLinkage::Imported)
            .map(|(&addr, symbol)| (addr, symbol.name.clone()))
            .collect();
        Ok(Self {
            symbols: canonical,
            imported_names,
        })
    }

    pub fn symbols(&self) -> impl ExactSizeIterator<Item = &FunctionSymbol> {
        self.symbols.values()
    }

    pub fn imported_names(&self) -> &HashMap<u64, String> {
        &self.imported_names
    }

    pub fn evidence_provenance(&self) -> FunctionSymbolEvidenceProvenance {
        FunctionSymbolEvidenceProvenance::RequestLocalAnalysis
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

    #[test]
    fn snapshot_is_canonical_and_imported_names_are_the_only_authority() {
        let first = FunctionSymbolSnapshot::try_from_symbols([
            FunctionSymbol {
                addr: 0x5000,
                name: "internal.memcpy".to_string(),
                linkage: FunctionSemanticLinkage::Internal,
            },
            FunctionSymbol {
                addr: 0x4000,
                name: "sym.imp.malloc".to_string(),
                linkage: FunctionSemanticLinkage::Imported,
            },
        ])
        .unwrap();
        let reordered = FunctionSymbolSnapshot::try_from_symbols([
            FunctionSymbol {
                addr: 0x4000,
                name: "sym.imp.malloc".to_string(),
                linkage: FunctionSemanticLinkage::Imported,
            },
            FunctionSymbol {
                addr: 0x5000,
                name: "internal.memcpy".to_string(),
                linkage: FunctionSemanticLinkage::Internal,
            },
        ])
        .unwrap();
        assert_eq!(first, reordered);
        assert_eq!(first.imported_names().len(), 1);
        assert_eq!(
            first.imported_names().get(&0x4000).map(String::as_str),
            Some("sym.imp.malloc")
        );
        assert!(!first.imported_names().contains_key(&0x5000));
    }

    #[test]
    fn snapshot_rejects_conflicting_duplicate_identity() {
        assert_eq!(
            FunctionSymbolSnapshot::try_from_symbols([
                FunctionSymbol {
                    addr: 0x4000,
                    name: "same".to_string(),
                    linkage: FunctionSemanticLinkage::Internal,
                },
                FunctionSymbol {
                    addr: 0x4000,
                    name: "same".to_string(),
                    linkage: FunctionSemanticLinkage::Imported,
                },
            ]),
            Err(FunctionSymbolSnapshotError::ConflictingDuplicate)
        );
    }
}
