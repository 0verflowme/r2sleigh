//! E2E test harness for r2sleigh.
//!
//! Provides utilities to run radare2 commands and validate plugin output.

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::{Mutex, MutexGuard, OnceLock};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;

fn r2_exec_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn lock_r2_exec() -> MutexGuard<'static, ()> {
    // Do not drop serialization after a panic in another test.
    r2_exec_lock().lock().unwrap_or_else(|e| e.into_inner())
}

/// Get path to vuln_test binary (handles both workspace root and tests/e2e dir)
pub fn vuln_test_binary() -> &'static str {
    if Path::new("vuln_test").exists() {
        "vuln_test"
    } else if Path::new("tests/e2e/vuln_test").exists() {
        "tests/e2e/vuln_test"
    } else {
        "vuln_test" // Let it fail with a clear message
    }
}

/// Get path to test_func binary
pub fn test_func_binary() -> &'static str {
    if Path::new("test_func").exists() {
        "test_func"
    } else if Path::new("tests/e2e/test_func").exists() {
        "tests/e2e/test_func"
    } else {
        "test_func"
    }
}

/// Get path to stress_test binary
pub fn stress_test_binary() -> &'static str {
    if Path::new("stress_test").exists() {
        "stress_test"
    } else if Path::new("tests/e2e/stress_test").exists() {
        "tests/e2e/stress_test"
    } else {
        "stress_test"
    }
}

/// Get path to optimized stress_test binary
pub fn stress_test_opt_binary() -> &'static str {
    if Path::new("stress_test_opt").exists() {
        "stress_test_opt"
    } else if Path::new("tests/e2e/stress_test_opt").exists() {
        "tests/e2e/stress_test_opt"
    } else {
        "stress_test_opt"
    }
}

/// Legacy constants for compatibility
pub const VULN_TEST_BINARY: &str = "vuln_test";
pub const TEST_FUNC_BINARY: &str = "test_func";

/// Result of running an r2 command
#[derive(Debug)]
pub struct R2Result {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: Option<i32>,
    pub crashed: bool,
    pub panicked: bool,
}

impl R2Result {
    /// Check if output contains expected pattern (regex-like grep match)
    pub fn contains(&self, pattern: &str) -> bool {
        self.stdout.contains(pattern) || self.stderr.contains(pattern)
    }

    /// Check if output contains any of the given patterns
    pub fn contains_any(&self, patterns: &[&str]) -> bool {
        patterns.iter().any(|p| self.contains(p))
    }

    /// Check if output contains all of the given patterns
    pub fn contains_all(&self, patterns: &[&str]) -> bool {
        patterns.iter().all(|p| self.contains(p))
    }

    /// Assert the command succeeded (no crash, no panic)
    pub fn assert_ok(&self) {
        assert!(
            !self.crashed,
            "Command crashed with exit code {:?}",
            self.exit_code
        );
        assert!(!self.panicked, "Command panicked: {}", self.stderr);
    }

    /// Try to parse stdout as JSON
    pub fn parse_json<T: serde::de::DeserializeOwned>(&self) -> Result<T, serde_json::Error> {
        serde_json::from_str(&self.stdout)
    }
}

/// Run radare2 with the given command on a binary
pub fn r2_cmd(binary: &str, cmd: &str) -> R2Result {
    r2_cmd_timeout(binary, cmd, Duration::from_secs(120))
}

/// Run radare2 with custom timeout
pub fn r2_cmd_timeout(binary: &str, cmd: &str, timeout: Duration) -> R2Result {
    run_r2_with_env(binary, cmd, scaled_timeout(timeout), &[], true)
}

/// Run radare2 without a timeout wrapper and with extra environment variables.
pub fn r2_cmd_with_env(binary: &str, cmd: &str, env: &[(&str, &str)]) -> R2Result {
    run_r2_with_env(
        binary,
        cmd,
        scaled_timeout(Duration::from_secs(120)),
        env,
        false,
    )
}

/// Run radare2 with custom timeout and extra environment variables.
pub fn r2_cmd_timeout_with_env(
    binary: &str,
    cmd: &str,
    timeout: Duration,
    env: &[(&str, &str)],
) -> R2Result {
    run_r2_with_env(binary, cmd, scaled_timeout(timeout), env, true)
}

fn run_r2_with_env(
    binary: &str,
    cmd: &str,
    timeout: Duration,
    env: &[(&str, &str)],
    use_timeout: bool,
) -> R2Result {
    let retries = parse_retry_count(std::env::var("R2SLEIGH_E2E_RETRIES").ok());
    for attempt in 0..=retries {
        let mut command = Command::new("r2");
        command.args(["-q", "-e", "bin.relocs.apply=true", "-c", cmd, binary]);
        configure_plugin_env(&mut command);

        for (key, value) in env {
            command.env(key, value);
        }

        let _guard = lock_r2_exec();
        let result = if use_timeout {
            run_command_with_timeout(command, timeout)
        } else {
            parse_output(command.output(), false)
        };

        if !should_retry_transient_crash(&result, attempt, retries) {
            return result;
        }
        thread::sleep(Duration::from_millis(50));
    }

    unreachable!("retry loop must return in all paths");
}

fn should_retry_transient_crash(result: &R2Result, attempt: u32, retries: u32) -> bool {
    // Retry only likely-transient signal exits; keep deterministic failures immediate.
    if attempt >= retries || result.panicked || !result.crashed {
        return false;
    }
    #[cfg(unix)]
    let signal_crash = result.exit_code.is_none();
    #[cfg(not(unix))]
    let signal_crash = matches!(result.exit_code, Some(134) | Some(136) | Some(137) | Some(139));
    signal_crash
}

fn parse_retry_count(raw: Option<String>) -> u32 {
    raw.as_deref()
        .and_then(|s| s.trim().parse::<u32>().ok())
        .filter(|&count| count <= 5)
        .unwrap_or(2)
}

/// Run r2 command seeking to a function first
pub fn r2_at_func(binary: &str, func: &str, cmd: &str) -> R2Result {
    let full_cmd = format!("aaa; s {}; {}", func, cmd);
    r2_cmd(binary, &full_cmd)
}

/// Run r2 command seeking to an address first  
pub fn r2_at_addr(binary: &str, addr: u64, cmd: &str) -> R2Result {
    let full_cmd = format!("aaa; s 0x{:x}; {}", addr, cmd);
    r2_cmd(binary, &full_cmd)
}

fn scaled_timeout(timeout: Duration) -> Duration {
    timeout
        .checked_mul(parse_timeout_factor(std::env::var("R2SLEIGH_E2E_TIMEOUT_FACTOR").ok()))
        .unwrap_or(Duration::MAX)
}

fn parse_timeout_factor(raw: Option<String>) -> u32 {
    raw.as_deref()
        .and_then(|s| s.trim().parse::<u32>().ok())
        .filter(|&factor| factor > 0)
        .unwrap_or(1)
}

fn configure_plugin_env(command: &mut Command) {
    #[cfg(target_os = "macos")]
    const RUST_PLUGIN_LIB: &str = "libr2sleigh_plugin.dylib";
    #[cfg(target_os = "linux")]
    const RUST_PLUGIN_LIB: &str = "libr2sleigh_plugin.so";
    #[cfg(target_os = "windows")]
    const RUST_PLUGIN_LIB: &str = "r2sleigh_plugin.dll";

    #[cfg(target_os = "windows")]
    const ANAL_PLUGIN_LIB: &str = "anal_sleigh.dll";
    #[cfg(target_os = "macos")]
    const ANAL_PLUGIN_LIB: &str = "anal_sleigh.dylib";
    #[cfg(all(not(target_os = "windows"), not(target_os = "macos")))]
    const ANAL_PLUGIN_LIB: &str = "anal_sleigh.so";
    const RUST_PLUGIN_SUBDIR: &str = "r2sleigh";

    static R2_HOME_OVERRIDE: OnceLock<Option<PathBuf>> = OnceLock::new();
    let home_override = R2_HOME_OVERRIDE.get_or_init(|| {
        let cwd = std::env::current_dir().ok()?;
        let mut plugin_src: Option<PathBuf> = None;
        for candidate in ["r2plugin", "../r2plugin", "../../r2plugin"] {
            let dir = cwd.join(candidate);
            if dir.join(ANAL_PLUGIN_LIB).exists()
                && dir.join(RUST_PLUGIN_SUBDIR).join(RUST_PLUGIN_LIB).exists()
            {
                plugin_src = Some(dir);
                break;
            }
        }
        let plugin_src = plugin_src?;
        let home_dir = std::env::temp_dir().join("r2sleigh-e2e-home");
        let plugin_dst = home_dir.join(".local/share/radare2/plugins");
        let runtime_dst = plugin_dst.join(RUST_PLUGIN_SUBDIR);
        fs::create_dir_all(&plugin_dst).ok()?;
        fs::create_dir_all(&runtime_dst).ok()?;
        fs::copy(
            plugin_src.join(ANAL_PLUGIN_LIB),
            plugin_dst.join(ANAL_PLUGIN_LIB),
        )
        .ok()?;
        fs::copy(
            plugin_src.join(RUST_PLUGIN_SUBDIR).join(RUST_PLUGIN_LIB),
            runtime_dst.join(RUST_PLUGIN_LIB),
        )
        .ok()?;
        #[cfg(not(target_os = "windows"))]
        {
            const ARCH_PLUGIN_LIB: &str = "arch_sleigh.so";
            if plugin_src.join(ARCH_PLUGIN_LIB).exists() {
                let _ = fs::copy(
                    plugin_src.join(ARCH_PLUGIN_LIB),
                    plugin_dst.join(ARCH_PLUGIN_LIB),
                );
            }
        }
        Some(home_dir)
    });
    if let Some(home_dir) = home_override {
        let plugins = home_dir.join(".local/share/radare2/plugins");
        command.env("HOME", home_dir);
        command.env("R2_USER_PLUGINS", plugins);
        return;
    }

    if let Ok(home) = std::env::var("HOME") {
        let plugin_dir = format!("{}/.local/share/radare2/plugins", home);
        command.env("R2_USER_PLUGINS", plugin_dir);
    }
}

fn run_command_with_timeout(mut command: Command, timeout: Duration) -> R2Result {
    command.stdout(Stdio::piped()).stderr(Stdio::piped());

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(err) => return parse_output(Err(err), false),
    };

    let stdout_reader = child.stdout.take().map(|mut stdout| {
        thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = stdout.read_to_end(&mut buf);
            buf
        })
    });
    let stderr_reader = child.stderr.take().map(|mut stderr| {
        thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = stderr.read_to_end(&mut buf);
            buf
        })
    });

    let start = Instant::now();
    let mut timed_out = false;
    let mut status = None;
    loop {
        match child.try_wait() {
            Ok(Some(s)) => {
                status = Some(s);
                break;
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    timed_out = true;
                    break;
                }
                thread::sleep(Duration::from_millis(10));
            }
            Err(err) => return parse_output(Err(err), false),
        }
    }

    if timed_out {
        let _ = child.kill();
    }

    let status = if timed_out {
        match child.wait() {
            Ok(s) => s,
            Err(err) => return parse_output(Err(err), timed_out),
        }
    } else {
        match status {
            Some(s) => s,
            None => {
                return parse_output(
                    Err(std::io::Error::other("missing child status")),
                    timed_out,
                );
            }
        }
    };

    let stdout = stdout_reader
        .and_then(|h| h.join().ok())
        .unwrap_or_default();
    let stderr = stderr_reader
        .and_then(|h| h.join().ok())
        .unwrap_or_default();
    let output = Output {
        status,
        stdout,
        stderr,
    };
    parse_output(Ok(output), timed_out)
}

fn parse_output(output: Result<Output, std::io::Error>, timed_out: bool) -> R2Result {
    match output {
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            let mut stderr = String::from_utf8_lossy(&out.stderr).to_string();
            let exit_code = out.status.code();

            // Detect real crashes: signal termination (SIGSEGV, SIGABRT, etc.) or
            // timeout-wrapper exit codes (128+signal).  Do NOT treat a plain non-zero
            // exit code as a crash — r2 legitimately returns non-zero sometimes.
            #[cfg(unix)]
            let crashed = timed_out
                || out.status.signal().is_some()
                || matches!(exit_code, Some(134) | Some(139) | Some(136) | Some(137));
            #[cfg(not(unix))]
            let crashed =
                timed_out || matches!(exit_code, Some(134) | Some(139) | Some(136) | Some(137));

            // Panic detection
            let panicked = stdout.contains("panicked")
                || stderr.contains("panicked")
                || stdout.contains("core dumped")
                || stderr.contains("core dumped");

            if timed_out {
                if !stderr.is_empty() {
                    stderr.push('\n');
                }
                stderr.push_str("r2 command timed out");
            }

            R2Result {
                stdout,
                stderr,
                exit_code,
                crashed,
                panicked,
            }
        }
        Err(e) => R2Result {
            stdout: String::new(),
            stderr: format!("Failed to execute r2: {}", e),
            exit_code: None,
            crashed: true,
            panicked: false,
        },
    }
}

/// Check that a test binary exists
pub fn require_binary(path: &str) {
    assert!(
        Path::new(path).exists(),
        "Test binary not found: {}. Compile it first.",
        path
    );
}

/// Check that the plugin is built
pub fn require_plugin() {
    let plugin_path = "target/release/libr2sleigh_plugin.so";
    assert!(
        Path::new(plugin_path).exists(),
        "Plugin not found at {}. Run `cargo build --release -p r2plugin` first.",
        plugin_path
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_timeout_factor_defaults_to_one() {
        assert_eq!(parse_timeout_factor(None), 1);
        assert_eq!(parse_timeout_factor(Some(String::new())), 1);
        assert_eq!(parse_timeout_factor(Some("bad".to_string())), 1);
        assert_eq!(parse_timeout_factor(Some("0".to_string())), 1);
    }

    #[test]
    fn parse_timeout_factor_accepts_positive_integer() {
        assert_eq!(parse_timeout_factor(Some("2".to_string())), 2);
        assert_eq!(parse_timeout_factor(Some("  4  ".to_string())), 4);
    }

}
