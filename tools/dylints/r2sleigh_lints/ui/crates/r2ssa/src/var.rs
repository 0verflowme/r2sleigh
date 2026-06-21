fn canonical_classifier(name: &str) -> bool {
    name.starts_with("tmp:")
}

fn main() {
    let _ = canonical_classifier("tmp:0");
}
