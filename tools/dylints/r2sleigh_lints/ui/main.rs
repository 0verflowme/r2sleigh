fn classify(name: &str) -> bool {
    name.starts_with("tmp:")
}

fn ordinary(name: &str) -> bool {
    name.starts_with("test_")
}

fn main() {
    let _ = classify("tmp:0x1000");
    let _ = ordinary("test_case");
}
