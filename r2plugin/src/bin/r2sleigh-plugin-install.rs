use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    if let Err(err) = run() {
        eprintln!("r2sleigh-plugin-install: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut rust_features: Option<String> = None;
    let mut rust_target: Option<String> = None;

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                print_help();
                return Ok(());
            }
            "--features" => {
                rust_features = Some(next_value(&mut args, "--features")?);
            }
            "--target" => {
                rust_target = Some(next_value(&mut args, "--target")?);
            }
            _ if arg.starts_with("--features=") => {
                rust_features = Some(arg["--features=".len()..].to_string());
            }
            _ if arg.starts_with("--target=") => {
                rust_target = Some(arg["--target=".len()..].to_string());
            }
            _ => return Err(format!("unknown argument: {arg}")),
        }
    }

    let plugin_dir = find_plugin_dir()
        .ok_or_else(|| "could not locate r2plugin directory; run from the repo root".to_string())?;

    let mut cmd = Command::new("make");
    cmd.arg("install").current_dir(&plugin_dir);
    if let Some(features) = rust_features {
        cmd.env("RUST_FEATURES", features);
    }
    if let Some(target) = rust_target {
        cmd.env("RUST_TARGET", target);
    }

    let status = cmd
        .status()
        .map_err(|err| format!("failed to run make: {err}"))?;
    if !status.success() {
        return Err(format!("make install failed ({status})"));
    }

    Ok(())
}

fn next_value(args: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, String> {
    args.next()
        .filter(|value| !value.is_empty())
        .ok_or_else(|| format!("missing value for {flag}"))
}

fn find_plugin_dir() -> Option<PathBuf> {
    let cwd = env::current_dir().ok()?;
    if is_plugin_dir(&cwd) {
        return Some(cwd);
    }
    let candidate = cwd.join("r2plugin");
    if is_plugin_dir(&candidate) {
        return Some(candidate);
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    if is_plugin_dir(&manifest_dir) {
        return Some(manifest_dir);
    }

    None
}

fn is_plugin_dir(path: &Path) -> bool {
    path.join("Makefile").is_file() && path.join("r_anal_sleigh.c").is_file()
}

fn print_help() {
    println!(
        "r2sleigh-plugin-install\n\n\
Usage:\n  r2sleigh-plugin-install [--features <list>] [--target <release|debug>]\n\n\
Options:\n  --features <list>  Sleigh features (x86, arm[ARM32+AArch64], mips, riscv, all-archs)\n  --target <name>    RUST_TARGET for Makefile (release or debug)\n  -h, --help         Show this help message"
    );
}
