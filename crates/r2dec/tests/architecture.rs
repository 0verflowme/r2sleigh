use std::fs;
use std::path::Path;

#[test]
fn analysis_never_imports_fold_in_production() {
    let analysis_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/analysis");
    let mut files = Vec::new();
    collect_rust_files(&analysis_dir, &mut files);
    files.sort();

    let mut violations = Vec::new();

    for file in files {
        let rel = relative_analysis_file(&analysis_dir, &file);
        let text = fs::read_to_string(&file).expect("analysis file should be UTF-8");
        for (line_idx, line) in production_lines(&text) {
            let trimmed = line.trim();
            if !trimmed.contains("crate::fold::") {
                continue;
            }

            violations.push(format!("{}:{} {}", rel, line_idx + 1, trimmed));
        }
    }

    assert!(
        violations.is_empty(),
        "r2dec::analysis must not import renderer-owned fold seams.\n\
         Move shared facts/policy into r2dec::analysis or an upstream crate first.\n\
         Violations:\n{}",
        violations.join("\n")
    );
}

fn relative_analysis_file(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

#[test]
fn production_has_no_legacy_name_identity_or_repair_answerers() {
    let source_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    collect_rust_files(&source_dir, &mut files);
    files.sort();

    let forbidden = [
        ("find_ssa_name_for_rendered_alias", "rendered-alias reverse lookup"),
        ("resolve_undeclared_carriers", "undeclared-carrier repair"),
        ("resolve_stack_var", "stack spelling identity lookup"),
        ("build_param_register_aliases", "positional parameter aliasing"),
        ("NameSource for", "parallel naming owner"),
        (".note_ssa_name(", "SSA-name side-table write"),
        ("fn note_ssa_name(", "SSA-name side-table owner"),
        (".for_ssa_name(", "SSA-name side-table lookup"),
        ("fn for_ssa_name(", "SSA-name side-table owner"),
        (
            "declare_assigned_names_without_a_declaration",
            "declare-after-render repair",
        ),
        ("spell_every_name_as_c", "post-render spelling answerer"),
        ("symbol::var_ref(", "generic spelling-to-symbol mint"),
        ("symbol::declare(", "generic spelling-to-symbol mint"),
        ("declare_or_reuse(", "generic spelling-to-symbol mint"),
    ];
    let mut violations = Vec::new();

    for file in files {
        let rel = file
            .strip_prefix(&source_dir)
            .unwrap_or(&file)
            .to_string_lossy()
            .replace('\\', "/");
        let text = fs::read_to_string(&file).expect("r2dec source file should be UTF-8");
        for (line_idx, line) in production_lines(&text) {
            let trimmed = line.trim();
            for (token, reason) in forbidden {
                if matches!(rel.as_str(), "symbol.rs" | "variable.rs")
                    && matches!(
                        token,
                        "symbol::var_ref(" | "symbol::declare(" | "declare_or_reuse("
                    )
                {
                    continue;
                }
                if trimmed.contains(token) {
                    violations.push(format!(
                        "{rel}:{} [{reason}] {trimmed}",
                        line_idx + 1
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "renderer production must consume sealed identities and presentation, \
         never reverse names or repair the final AST. Violations:\n{}",
        violations.join("\n")
    );
}

/// Lines outside `#[cfg(test)]` items, retaining zero-based source line numbers.
/// Test items are skipped rather than treated as EOF so a production item
/// placed after one cannot hide from an architecture interlock.
fn production_lines(text: &str) -> Vec<(usize, &str)> {
    let lines = text.lines().collect::<Vec<_>>();
    if lines
        .iter()
        .find(|line| !line.trim().is_empty())
        .is_some_and(|line| line.trim() == "#![cfg(test)]")
    {
        return Vec::new();
    }
    let mut production = Vec::new();
    let mut index = 0usize;
    while index < lines.len() {
        if lines[index].trim() == "#[cfg(test)]" {
            let mut depth = 0isize;
            let mut opened = false;
            index += 1;
            let item_head = lines.get(index).map_or("", |line| line.trim_start());
            let expects_brace = item_head.starts_with("mod ")
                || item_head.starts_with("impl ")
                || item_head.starts_with("struct ")
                || item_head.starts_with("enum ")
                || item_head.starts_with("trait ")
                || item_head.starts_with("fn ")
                || item_head.contains(" fn ");
            while index < lines.len() {
                for byte in lines[index].bytes() {
                    match byte {
                        b'{' => {
                            depth += 1;
                            opened = true;
                        }
                        b'}' => depth -= 1,
                        _ => {}
                    }
                }
                let terminal = lines[index].trim_end();
                index += 1;
                if opened && depth == 0 {
                    break;
                }
                if !opened
                    && (terminal.ends_with(';') || (!expects_brace && terminal.ends_with(',')))
                {
                    break;
                }
            }
            continue;
        }
        production.push((index, lines[index]));
        index += 1;
    }
    production
}

fn collect_rust_files(directory: &Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries = fs::read_dir(directory)
        .expect("r2dec source directory should be readable")
        .map(|entry| entry.expect("r2dec source entry should be readable").path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_rust_files(&path, out);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            out.push(path);
        }
    }
}
