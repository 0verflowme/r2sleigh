use std::collections::HashMap;

use serde::Deserialize;

use crate::model::{Signedness, TypeArena, TypeId};

#[derive(Debug, Clone)]
pub struct ResolvedSignature {
    pub ret: TypeId,
    pub params: Vec<TypeId>,
    pub variadic: bool,
}

#[derive(Debug, Clone, Default)]
pub struct SignatureRegistry {
    entries: HashMap<String, SignatureEntry>,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
struct SignatureFile {
    version: u32,
    #[serde(default)]
    signatures: HashMap<String, SignatureEntry>,
}

#[derive(Debug, Clone, Deserialize)]
struct SignatureEntry {
    #[serde(default, rename = "return")]
    ret: String,
    #[serde(default)]
    params: Vec<String>,
    #[serde(default)]
    variadic: bool,
}

impl SignatureRegistry {
    pub fn from_embedded_json() -> Self {
        let mut registry = Self::default();

        for (name, content) in [
            (
                "libc.v1.json",
                include_str!("../data/signatures/libc.v1.json"),
            ),
            (
                "posix.v1.json",
                include_str!("../data/signatures/posix.v1.json"),
            ),
            (
                "win32.v1.json",
                include_str!("../data/signatures/win32.v1.json"),
            ),
        ] {
            registry.load_file(name, content);
        }

        if registry.entries.is_empty() {
            registry
                .diagnostics
                .push("signature registry empty; using fallback built-ins".to_string());
            registry.seed_fallbacks();
        }

        registry
    }

    fn load_file(&mut self, source_name: &str, content: &str) {
        match serde_json::from_str::<SignatureFile>(content) {
            Ok(file) => {
                if file.version != 1 {
                    self.diagnostics.push(format!(
                        "signature file {} has unsupported version {}",
                        source_name, file.version
                    ));
                    return;
                }
                for (name, sig) in file.signatures {
                    self.entries.insert(normalize_name(&name), sig);
                }
            }
            Err(e) => {
                self.diagnostics
                    .push(format!("failed to parse {}: {}", source_name, e));
            }
        }
    }

    fn seed_fallbacks(&mut self) {
        let fallback = [
            (
                "printf",
                SignatureEntry {
                    ret: "i32".to_string(),
                    params: vec!["char*".to_string()],
                    variadic: true,
                },
            ),
            (
                "memcpy",
                SignatureEntry {
                    ret: "void*".to_string(),
                    params: vec![
                        "void*".to_string(),
                        "void*".to_string(),
                        "size_t".to_string(),
                    ],
                    variadic: false,
                },
            ),
            (
                "strlen",
                SignatureEntry {
                    ret: "size_t".to_string(),
                    params: vec!["char*".to_string()],
                    variadic: false,
                },
            ),
            (
                "setlocale",
                SignatureEntry {
                    ret: "char*".to_string(),
                    params: vec!["i32".to_string(), "char*".to_string()],
                    variadic: false,
                },
            ),
        ];

        for (name, sig) in fallback {
            self.entries.insert(normalize_name(name), sig);
        }
    }

    pub fn resolve(
        &self,
        name: &str,
        arena: &mut TypeArena,
        ptr_bits: u32,
    ) -> Option<ResolvedSignature> {
        let key = normalize_name(name);
        let entry = self.entries.get(&key)?;

        let params = entry
            .params
            .iter()
            .map(|spec| parse_type_spec(spec, arena, ptr_bits))
            .collect();
        let ret = parse_type_spec(&entry.ret, arena, ptr_bits);

        Some(ResolvedSignature {
            ret,
            params,
            variadic: entry.variadic,
        })
    }

    pub fn insert_raw(
        &mut self,
        name: &str,
        ret: impl Into<String>,
        params: Vec<String>,
        variadic: bool,
    ) {
        self.entries.insert(
            normalize_name(name),
            SignatureEntry {
                ret: ret.into(),
                params,
                variadic,
            },
        );
    }
}

fn normalize_name(name: &str) -> String {
    let mut normalized = name.trim().to_ascii_lowercase();

    // "flirt." is what a signature match prepends, so a matched libc function
    // has to lose it before it can be looked up as that libc function.
    for prefix in ["sym.imp.", "sym.", "imp.", "dbg.", "flirt."] {
        while let Some(rest) = normalized.strip_prefix(prefix) {
            normalized = rest.to_string();
        }
    }
    while let Some(rest) = normalized.strip_suffix("@plt") {
        normalized = rest.to_string();
    }
    while let Some(rest) = normalized.strip_suffix(".plt") {
        normalized = rest.to_string();
    }

    normalized
}

pub fn parse_type_spec(spec: &str, arena: &mut TypeArena, ptr_bits: u32) -> TypeId {
    let mut text = spec.trim().to_ascii_lowercase();
    if text.is_empty() {
        return arena.top();
    }

    let mut ptr_depth = 0usize;
    while let Some(rest) = text.strip_suffix('*') {
        text = rest.trim_end().to_string();
        ptr_depth += 1;
    }

    let base = match text.as_str() {
        "void" => arena.unknown_alias("void"),
        "bool" => arena.bool_ty(),
        "char" | "i8" | "int8_t" => arena.int(8, Signedness::Signed),
        "u8" | "uint8_t" | "unsigned char" => arena.int(8, Signedness::Unsigned),
        "i16" | "int16_t" | "short" | "short int" => arena.int(16, Signedness::Signed),
        "u16" | "uint16_t" | "unsigned short" | "unsigned short int" => {
            arena.int(16, Signedness::Unsigned)
        }
        "i32" | "int32_t" | "int" => arena.int(32, Signedness::Signed),
        "u32" | "uint32_t" | "unsigned" | "unsigned int" => arena.int(32, Signedness::Unsigned),
        "i64" | "int64_t" | "long" | "long int" | "long long" | "long long int" => {
            arena.int(ptr_bits, Signedness::Signed)
        }
        "u64"
        | "uint64_t"
        | "unsigned long"
        | "unsigned long int"
        | "unsigned long long"
        | "unsigned long long int"
        | "size_t" => arena.int(ptr_bits, Signedness::Unsigned),
        "float" => arena.float(32),
        "double" => arena.float(64),
        other if other.starts_with("struct ") => {
            arena.struct_named_or_existing(other.trim_start_matches("struct "))
        }
        other if other.starts_with("union ") || other.starts_with("enum ") => {
            arena.unknown_alias(other.to_string())
        }
        _ => arena.unknown_alias(text),
    };

    let mut ty = base;
    for _ in 0..ptr_depth {
        ty = arena.ptr(ty);
    }
    ty
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embedded_registry_loads_known_signatures() {
        let mut arena = TypeArena::default();
        let registry = SignatureRegistry::from_embedded_json();
        let sig = registry
            .resolve("sym.imp.printf", &mut arena, 64)
            .expect("printf signature missing");
        assert_eq!(sig.params.len(), 1);
        assert!(sig.variadic);
    }

    #[test]
    fn parse_type_spec_handles_pointers() {
        let mut arena = TypeArena::default();
        let ty = parse_type_spec("char**", &mut arena, 64);
        let first = match arena.get(ty) {
            crate::model::Type::Ptr(inner) => *inner,
            _ => panic!("expected pointer"),
        };
        assert!(matches!(arena.get(first), crate::model::Type::Ptr(_)));
    }
}
