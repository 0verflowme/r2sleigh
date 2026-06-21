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
