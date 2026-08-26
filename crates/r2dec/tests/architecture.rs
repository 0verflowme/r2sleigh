use std::fs;
use std::path::Path;

#[test]
fn analysis_never_imports_fold_in_production() {
    let analysis_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/analysis");
    let mut files = fs::read_dir(&analysis_dir)
        .expect("analysis directory should exist")
        .map(|entry| {
            entry
                .expect("analysis file entry should be readable")
                .path()
        })
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect::<Vec<_>>();
    files.sort();

    let mut violations = Vec::new();

    for file in files {
        let rel = relative_analysis_file(&analysis_dir, &file);
        let text = fs::read_to_string(&file).expect("analysis file should be UTF-8");
        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed == "#[cfg(test)]" {
                break;
            }
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
        ("impl NameSource", "parallel naming owner"),
        (".note_ssa_name(", "SSA-name side-table write"),
        ("fn note_ssa_name(", "SSA-name side-table owner"),
        (".for_ssa_name(", "SSA-name side-table lookup"),
        ("fn for_ssa_name(", "SSA-name side-table owner"),
        (
            "declare_assigned_names_without_a_declaration",
            "declare-after-render repair",
        ),
        ("spell_every_name_as_c", "post-render spelling answerer"),
    ];
    let mut violations = Vec::new();

    for file in files {
        let rel = file
            .strip_prefix(&source_dir)
            .unwrap_or(&file)
            .to_string_lossy()
            .replace('\\', "/");
        let text = fs::read_to_string(&file).expect("r2dec source file should be UTF-8");
        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed == "#[cfg(test)]" {
                break;
            }
            for (token, reason) in forbidden {
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
