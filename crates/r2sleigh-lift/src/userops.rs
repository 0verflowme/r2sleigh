use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

static USEROP_CACHE: OnceLock<Mutex<HashMap<String, HashMap<u32, String>>>> = OnceLock::new();

fn arch_to_slaspec(arch: &str) -> Option<(&'static str, &'static str)> {
    match arch.to_ascii_lowercase().as_str() {
        "x86-64" | "x86_64" | "x64" | "amd64" => Some(("x86", "x86-64.slaspec")),
        "x86" | "x86-32" | "i386" | "i686" => Some(("x86", "x86.slaspec")),
        "arm" | "arm32" | "arm-le" => Some(("ARM", "ARM8_le.slaspec")),
        "aarch64" | "arm64" | "arm64e" => Some(("AARCH64", "AARCH64_AppleSilicon.slaspec")),
        "mips" | "mips32" | "mips32be" | "mipsbe" | "mipseb" => Some(("MIPS", "mips32be.slaspec")),
        "mipsel" | "mips32le" | "mips32el" => Some(("MIPS", "mips32le.slaspec")),
        "mips64" | "mips64be" => Some(("MIPS", "mips64be.slaspec")),
        "mips64el" | "mips64le" => Some(("MIPS", "mips64le.slaspec")),
        "riscv64" | "rv64" | "rv64gc" => Some(("RISCV", "riscv.lp64d.slaspec")),
        "riscv32" | "rv32" | "rv32gc" => Some(("RISCV", "riscv.ilp32d.slaspec")),
        _ => None,
    }
}

fn find_sleigh_config_root() -> Option<PathBuf> {
    if let Ok(root) = env::var("SLEIGH_CONFIG_ROOT") {
        let path = PathBuf::from(root);
        if path.join("ghidra/Ghidra/Processors").exists() {
            return Some(path);
        }
    }

    let cargo_home = env::var("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|_| env::var("HOME").map(|home| PathBuf::from(home).join(".cargo")))
        .ok()?;
    let registry_src = cargo_home.join("registry").join("src");
    let entries = fs::read_dir(registry_src).ok()?;

    let mut candidates = Vec::new();
    for entry in entries.filter_map(Result::ok) {
        if entry.path().is_dir() {
            candidates.push(entry.path());
        }
    }
    candidates.sort();

    for root in candidates {
        let registry_entries = fs::read_dir(&root).ok()?;
        let mut configs = Vec::new();
        for entry in registry_entries.filter_map(Result::ok) {
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().to_string();
            if name.starts_with("sleigh-config-") && path.is_dir() {
                configs.push(path);
            }
        }
        configs.sort();
        for config in configs {
            if config.join("ghidra/Ghidra/Processors").exists() {
                return Some(config);
            }
        }
    }

    None
}

fn parse_include(line: &str) -> Option<String> {
    let trimmed = line.trim_start();
    if !(trimmed.starts_with("@include") || trimmed.starts_with("include")) {
        return None;
    }

    let start = trimmed.find('"')?;
    let rest = &trimmed[start + 1..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn parse_pcodeop(line: &str) -> Option<String> {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    if tokens.len() < 3 {
        return None;
    }
    if tokens[0] != "define" || tokens[1] != "pcodeop" {
        return None;
    }

    let mut name = tokens[2].trim_end_matches(';').trim_end_matches(',');
    if name.is_empty() {
        return None;
    }
    if let Some((head, _)) = name.split_once(';') {
        name = head;
    }
    Some(name.to_string())
}

fn parse_userops_from_file(
    path: &Path,
    seen: &mut HashSet<PathBuf>,
    out: &mut Vec<String>,
) -> std::io::Result<()> {
    let path = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    if !seen.insert(path.clone()) {
        return Ok(());
    }

    let content = fs::read_to_string(&path)?;
    let base_dir = path.parent().unwrap_or_else(|| Path::new("."));

    for raw_line in content.lines() {
        let no_hash = raw_line.split('#').next().unwrap_or("");
        let line = no_hash.split("//").next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }

        if let Some(include) = parse_include(line) {
            let include_path = base_dir.join(include);
            let _ = parse_userops_from_file(&include_path, seen, out);
        }

        if let Some(name) = parse_pcodeop(line) {
            out.push(name);
        }
    }

    Ok(())
}

fn build_userop_map(arch: &str) -> HashMap<u32, String> {
    let mut map = HashMap::new();
    let Some((processor, slaspec)) = arch_to_slaspec(arch) else {
        return map;
    };

    let Some(root) = find_sleigh_config_root() else {
        return map;
    };

    let slaspec_path = root
        .join("ghidra/Ghidra/Processors")
        .join(processor)
        .join("data/languages")
        .join(slaspec);

    let mut names = Vec::new();
    let mut seen = HashSet::new();
    if parse_userops_from_file(&slaspec_path, &mut seen, &mut names).is_err() {
        return map;
    }

    for (index, name) in names.into_iter().enumerate() {
        map.insert(index as u32, name);
    }

    map
}

pub fn userop_map_for_arch(arch: &str) -> HashMap<u32, String> {
    let key = arch.to_ascii_lowercase();
    let cache = USEROP_CACHE.get_or_init(|| Mutex::new(HashMap::new()));

    // Check cache first (quick path with short lock hold)
    if let Ok(guard) = cache.lock()
        && let Some(found) = guard.get(&key)
    {
        return found.clone();
    }

    // Build outside lock - this may do file I/O which can be slow.
    // We don't want to block other threads waiting for the cache.
    let map = build_userop_map(&key);

    // Insert into cache (another thread may have raced us, that's OK)
    if let Ok(mut guard) = cache.lock() {
        guard.entry(key).or_insert_with(|| map.clone());
    }

    map
}
