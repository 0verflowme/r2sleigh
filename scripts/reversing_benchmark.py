#!/usr/bin/env python3
"""Deterministic reversing benchmark harness for r2sleigh.

The harness does not download or commit corpora. It consumes local binaries from
repo fixtures, optional public-corpus directories, a manifest, and an optional
kernelcache path, then emits a sorted JSON report that can drive product work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Optional


SCHEMA_VERSION = 2
DEFAULT_TMPDIR = "/tmp/r2sleigh-reversing-benchmark-tmp"
DEFAULT_OUT = "/tmp/r2sleigh-reversing-benchmark.json"
DEFAULT_MAX_BINARIES_PER_CORPUS = 8
DEFAULT_MAX_FUNCTIONS = 6
DEFAULT_TIMEOUT = 180
DEFAULT_ANALYSIS = "aaa"
DECOMPILER_FALLBACK_MARKERS = (
    "r2dec fallback:",
    "r2dec: decompilation panicked",
    "r2dec: failed to spawn",
    "skipped decompilation",
    "r2pm -ci r2dec",
)
RESIDUAL_MARKERS = ("budget", "residual", "largecfg", "large cfg", "timeout")
TEMP_ARTIFACT_RE = re.compile(
    r"\b(?:tmp[:_][A-Za-z0-9_:.]+|unique[:_][A-Za-z0-9_:.]+|unk_[A-Za-z0-9_]+|"
    r"(?:SP|FP|LR|PC|X[0-9]+|R[0-9A-Z]+)_[0-9]+)\b"
)
GENERIC_NAME_RE = re.compile(r"^(?:arg|param|var)[._]?[0-9]+$", re.IGNORECASE)
GENERIC_TYPE_RE = re.compile(
    r"(?:\b(?:unknown|undefined|unk|uint(?:32|64)_t|int(?:32|64)_t)\b|void\s*\*)",
    re.IGNORECASE,
)
COREUTILS_PRIORITY = (
    "ls",
    "cp",
    "mv",
    "rm",
    "sort",
    "uniq",
    "cut",
    "dd",
    "sha256sum",
    "wc",
    "printf",
    "test",
)
REPO_FIXTURES = (
    {
        "name": "vuln_test_x86",
        "path": "tests/e2e/vuln_test_x86",
        "corpus": "repo-fixtures",
        "targets": ["check_secret", "process_string", "alloc_and_copy", "test_boolxor"],
    },
    {
        "name": "stress_test_x86",
        "path": "tests/e2e/stress_test_x86",
        "corpus": "repo-fixtures",
        "targets": ["parse_number", "tiny_vm_dispatch"],
    },
    {
        "name": "test_func_x86",
        "path": "tests/e2e/test_func_x86",
        "corpus": "repo-fixtures",
        "targets": ["alloc_wrapper2", "large_basic_block_guard"],
    },
)
KERNEL_TARGETS = (
    "_IOMalloc",
    "_IOFree",
    "_copyin",
    "_copyout",
    "_kalloc_type_impl",
    "_kfree_type_impl",
    "_lck_mtx_lock",
    "_lck_mtx_unlock",
    "_os_ref_retain",
    "_os_ref_release",
)


@dataclass(frozen=True)
class CmdResult:
    returncode: int
    stdout: str
    stderr: str
    elapsed_s: float


@dataclass(frozen=True)
class BinaryCase:
    name: str
    path: Path
    corpus: str
    analysis: str
    targets: tuple[str, ...]
    max_functions: int


Runner = Callable[[str, Path, str, int, Optional[dict[str, str]]], CmdResult]


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def default_r2_path() -> str:
    for env_name in ("R2SLEIGH_E2E_RADARE2", "R2R_RADARE2"):
        value = os.environ.get(env_name, "").strip()
        if value:
            return value
    for candidate in (
        "../radare2/binr/radare2/radare2",
        "../../radare2/binr/radare2/radare2",
        "/private/tmp/radare2-r2sleigh-clean/binr/radare2/radare2",
        "/Users/priyanshu/code/radare2/binr/radare2/radare2",
    ):
        if Path(candidate).exists():
            return candidate
    return "radare2"


def default_plugin_dir() -> str:
    for env_name in ("R2SLEIGH_PLUGIN_DIR", "R2R_PLUGIN_DIR", "R2_LIBR_PLUGINS"):
        value = os.environ.get(env_name, "").strip()
        if value:
            return value
    if sys.platform == "darwin":
        shared_ext = "dylib"
        rust_plugin = f"libr2sleigh_plugin.{shared_ext}"
    elif sys.platform == "win32":
        shared_ext = "dll"
        rust_plugin = "r2sleigh_plugin.dll"
    else:
        shared_ext = "so"
        rust_plugin = f"libr2sleigh_plugin.{shared_ext}"
    for candidate in (Path("r2plugin"), Path("../r2plugin"), Path("../../r2plugin")):
        if (
            candidate.joinpath(f"anal_sleigh.{shared_ext}").exists()
            and candidate.joinpath("r2sleigh", rust_plugin).exists()
        ):
            return str(candidate)
    return ""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run deterministic r2sleigh reversing benchmarks over local corpora."
    )
    parser.add_argument("--r2", default=default_r2_path(), help="radare2 executable path")
    parser.add_argument(
        "--plugin-dir",
        default=default_plugin_dir(),
        help="radare2 plugin directory for isolated benchmark runs",
    )
    parser.add_argument(
        "--tmpdir",
        default=os.environ.get("R2SLEIGH_BENCH_TMPDIR", DEFAULT_TMPDIR),
        help="temporary HOME/XDG/TMP root for radare2 subprocesses",
    )
    parser.add_argument(
        "--out",
        default=DEFAULT_OUT,
        help="JSON report output path",
    )
    parser.add_argument(
        "--analysis",
        choices=("aa", "aaa", "aaaa"),
        default=DEFAULT_ANALYSIS,
        help="native radare2 analysis depth for benchmark cases",
    )
    parser.add_argument(
        "--manifest",
        default="",
        help="optional JSON manifest with a top-level 'binaries' array",
    )
    parser.add_argument(
        "--binary",
        action="append",
        default=[],
        help="additional binary path to benchmark; may be repeated",
    )
    parser.add_argument(
        "--target",
        action="append",
        default=[],
        help="global target function name; may be repeated",
    )
    parser.add_argument(
        "--coreutils-dir",
        default=os.environ.get("R2SLEIGH_COREUTILS_DIR", ""),
        help="directory containing coreutils binaries",
    )
    parser.add_argument(
        "--cgc-dir",
        default=os.environ.get("R2SLEIGH_CGC_DIR", ""),
        help="directory containing DARPA CGC binaries",
    )
    parser.add_argument(
        "--juliet-dir",
        default=os.environ.get("R2SLEIGH_JULIET_DIR", ""),
        help="directory containing compiled Juliet binaries",
    )
    parser.add_argument(
        "--kernel",
        default=os.environ.get("R2SLEIGH_KERNELCACHE", ""),
        help="optional local kernelcache path; never committed",
    )
    parser.add_argument(
        "--no-repo-fixtures",
        action="store_true",
        help="do not auto-add tests/e2e fixture binaries",
    )
    parser.add_argument(
        "--max-binaries-per-corpus",
        type=int,
        default=DEFAULT_MAX_BINARIES_PER_CORPUS,
        help="maximum executables scanned from each external corpus directory",
    )
    parser.add_argument(
        "--max-functions",
        type=int,
        default=DEFAULT_MAX_FUNCTIONS,
        help="maximum discovered functions sampled per binary when no target is matched",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=1,
        help="repeat per-function reports to detect output nondeterminism",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help="per-radare2 command timeout in seconds",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="return non-zero when benchmark failures are detected",
    )
    parser.add_argument(
        "--include-sensitive",
        action="store_true",
        help="include local paths and output previews in the report",
    )
    return parser.parse_args()


def is_executable(path: Path) -> bool:
    try:
        mode = path.stat().st_mode
    except OSError:
        return False
    return path.is_file() and bool(mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH))


def normalize_symbol(name: str) -> str:
    for prefix in ("sym.", "dbg.", "imp."):
        if name.startswith(prefix):
            name = name[len(prefix) :]
    return name.lstrip("_").lower()


def redacted_path(path: Path) -> str:
    return f"<redacted:{path.name}>"


def display_path(path: Path, include_sensitive: bool) -> str:
    return str(path) if include_sensitive else redacted_path(path)


def parse_json_payload(text: str) -> Any:
    stripped = text.strip()
    if not stripped:
        raise ValueError("empty output")
    decoder = json.JSONDecoder()
    for idx, ch in enumerate(stripped):
        if ch not in "[{":
            continue
        try:
            payload, _ = decoder.raw_decode(stripped[idx:])
            return payload
        except json.JSONDecodeError:
            continue
    raise ValueError("no JSON payload found")


def summarize_text(text: str, *, include_preview: bool, max_lines: int = 40) -> dict[str, Any]:
    data = text.encode("utf-8", "replace")
    lines = text.splitlines()
    summary: dict[str, Any] = {
        "bytes": len(data),
        "lines": len(lines),
        "sha256": hashlib.sha256(data).hexdigest(),
        "truncated": len(lines) > max_lines,
    }
    if include_preview:
        summary["preview"] = lines[:max_lines]
    return summary


def decompiler_fallback_marker(text: str) -> str | None:
    lower = text.lower()
    if "r2dec budget:" in lower or "r2dec residual:" in lower:
        return None
    for marker in DECOMPILER_FALLBACK_MARKERS:
        if marker.lower() in lower:
            return marker
    return None


def residual_marker_count(text: str) -> int:
    lower = text.lower()
    return sum(lower.count(marker) for marker in RESIDUAL_MARKERS)


def runtime_bucket(elapsed_s: float) -> str:
    if elapsed_s < 1.0:
        return "fast"
    if elapsed_s < 5.0:
        return "normal"
    if elapsed_s < 15.0:
        return "slow"
    return "hot"


def artifact_density(text: str) -> dict[str, Any]:
    lines = [line for line in text.splitlines() if line.strip()]
    matches = TEMP_ARTIFACT_RE.findall(text)
    line_count = max(1, len(lines))
    return {
        "artifact_count": len(matches),
        "per_line": round(len(matches) / line_count, 6),
    }


def decompile_quality(text: str) -> dict[str, Any]:
    fallback = decompiler_fallback_marker(text)
    residuals = residual_marker_count(text)
    empty = len(text.strip()) == 0
    if empty:
        classification = "empty"
    elif fallback:
        classification = "fallback"
    elif residuals:
        classification = "residual"
    else:
        classification = "structured"
    metrics = artifact_density(text)
    metrics.update(
        {
            "classification": classification,
            "fallback_marker": fallback,
            "residual_markers": residuals,
            "empty": empty,
        }
    )
    return metrics


def generic_type_metrics(payload: dict[str, Any]) -> dict[str, int]:
    generic_arg_count = 0
    generic_type_count = 0

    def inspect_name_type(name: Any, typ: Any) -> None:
        nonlocal generic_arg_count, generic_type_count
        if isinstance(name, str) and GENERIC_NAME_RE.search(normalize_symbol(name)):
            generic_arg_count += 1
        if isinstance(typ, str) and GENERIC_TYPE_RE.search(typ):
            generic_type_count += 1

    inspect_name_type(payload.get("name"), payload.get("ret_type"))
    params = payload.get("params")
    if isinstance(params, list):
        for param in params:
            if not isinstance(param, dict):
                continue
            inspect_name_type(param.get("name") or param.get("reg"), param.get("type") or param.get("ctype"))
    locals_payload = payload.get("locals")
    if isinstance(locals_payload, list):
        for local in locals_payload:
            if isinstance(local, dict):
                inspect_name_type(local.get("name"), local.get("type") or local.get("ctype"))
    return {
        "generic_arg_count": generic_arg_count,
        "generic_type_count": generic_type_count,
    }


def local_radare2_library_path(r2: str) -> str:
    override = os.environ.get("R2SLEIGH_BENCH_R2_LIB_PATH", "").strip()
    if override:
        return override
    binary = Path(r2)
    if not binary.exists():
        return ""
    root = binary.parent.parent.parent
    libr = root / "libr"
    if not libr.is_dir():
        return ""
    dirs = sorted(path for path in libr.iterdir() if path.is_dir())
    return ":".join(str(path) for path in dirs)


def build_r2_env(r2: str, plugin_dir: str, tmpdir: Path | None) -> dict[str, str]:
    env = os.environ.copy()
    if plugin_dir:
        env["R2_USER_PLUGINS"] = plugin_dir
        env["R2_LIBR_PLUGINS"] = plugin_dir
    if tmpdir is not None:
        tmpdir.mkdir(parents=True, exist_ok=True)
        home = tmpdir / "home"
        xdg_data = tmpdir / "xdg-data"
        home.mkdir(parents=True, exist_ok=True)
        xdg_data.mkdir(parents=True, exist_ok=True)
        env["HOME"] = str(home)
        env["TMPDIR"] = str(tmpdir)
        env["TMP"] = str(tmpdir)
        env["TEMP"] = str(tmpdir)
        env["XDG_DATA_HOME"] = str(xdg_data)
    lib_path = local_radare2_library_path(r2)
    if lib_path:
        env["LD_LIBRARY_PATH"] = prepend_path(lib_path, env.get("LD_LIBRARY_PATH", ""))
        if sys.platform == "darwin":
            env["DYLD_LIBRARY_PATH"] = prepend_path(lib_path, env.get("DYLD_LIBRARY_PATH", ""))
    return env


def prepend_path(prefix: str, existing: str) -> str:
    if not existing:
        return prefix
    return f"{prefix}:{existing}"


def run_r2(
    r2: str,
    binary: Path,
    cmd: str,
    timeout_s: int,
    env: dict[str, str] | None = None,
) -> CmdResult:
    argv = [
        r2,
        "-q",
        "-e",
        "scr.color=false",
        "-e",
        "log.level=0",
        "-e",
        "bin.relocs.apply=true",
        "-c",
        cmd,
        str(binary),
    ]
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            argv,
            capture_output=True,
            text=True,
            timeout=timeout_s,
            check=False,
            env=env,
        )
        return CmdResult(
            returncode=proc.returncode,
            stdout=proc.stdout,
            stderr=proc.stderr,
            elapsed_s=time.perf_counter() - start,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        return CmdResult(
            returncode=124,
            stdout=stdout,
            stderr=stderr or f"timeout after {timeout_s}s",
            elapsed_s=time.perf_counter() - start,
        )


def read_manifest(path: Path, default_analysis: str, default_max_functions: int) -> list[BinaryCase]:
    payload = json.loads(path.read_text())
    binaries = payload.get("binaries", []) if isinstance(payload, dict) else []
    cases: list[BinaryCase] = []
    for item in binaries:
        if not isinstance(item, dict):
            continue
        raw_path = item.get("path")
        if not isinstance(raw_path, str) or not raw_path:
            continue
        binary_path = Path(raw_path)
        if not binary_path.is_absolute():
            binary_path = path.parent / binary_path
        name = item.get("name") if isinstance(item.get("name"), str) else binary_path.name
        corpus = item.get("corpus") if isinstance(item.get("corpus"), str) else "manifest"
        analysis = item.get("analysis") if item.get("analysis") in ("aa", "aaa", "aaaa") else default_analysis
        targets = tuple(str(t) for t in item.get("targets", []) if str(t).strip())
        max_functions = int(item.get("max_functions", default_max_functions))
        cases.append(
            BinaryCase(
                name=name,
                path=binary_path,
                corpus=corpus,
                analysis=analysis,
                targets=targets,
                max_functions=max_functions,
            )
        )
    return cases


def repo_fixture_cases(default_analysis: str, default_max_functions: int) -> list[BinaryCase]:
    root = repo_root()
    cases: list[BinaryCase] = []
    for fixture in REPO_FIXTURES:
        path = root / str(fixture["path"])
        if not path.exists():
            continue
        cases.append(
            BinaryCase(
                name=str(fixture["name"]),
                path=path,
                corpus=str(fixture["corpus"]),
                analysis=default_analysis,
                targets=tuple(str(t) for t in fixture["targets"]),
                max_functions=default_max_functions,
            )
        )
    return cases


def direct_binary_cases(
    paths: list[str],
    targets: list[str],
    default_analysis: str,
    default_max_functions: int,
) -> list[BinaryCase]:
    cases: list[BinaryCase] = []
    for raw in paths:
        path = Path(raw)
        cases.append(
            BinaryCase(
                name=path.name,
                path=path,
                corpus="manual",
                analysis=default_analysis,
                targets=tuple(targets),
                max_functions=default_max_functions,
            )
        )
    return cases


def scan_executables(root: Path, limit: int, priority: tuple[str, ...] = ()) -> list[Path]:
    if not root.exists():
        return []
    direct = [root / name for name in priority if is_executable(root / name)]
    direct_seen = {path.resolve() for path in direct}
    rest = [
        path
        for path in root.rglob("*")
        if is_executable(path) and path.resolve() not in direct_seen
    ]
    rest.sort(key=lambda path: (len(path.parts), str(path)))
    return (direct + rest)[: max(0, limit)]


def external_corpus_cases(
    corpus: str,
    root_value: str,
    limit: int,
    default_analysis: str,
    default_max_functions: int,
) -> list[BinaryCase]:
    if not root_value:
        return []
    root = Path(root_value)
    priority = COREUTILS_PRIORITY if corpus == "coreutils" else ()
    paths = scan_executables(root, limit, priority=priority)
    return [
        BinaryCase(
            name=path.name,
            path=path,
            corpus=corpus,
            analysis=default_analysis,
            targets=(),
            max_functions=default_max_functions,
        )
        for path in paths
    ]


def kernel_case(
    kernel: str,
    default_analysis: str,
    default_max_functions: int,
) -> list[BinaryCase]:
    if not kernel:
        return []
    return [
        BinaryCase(
            name="kernelcache",
            path=Path(kernel),
            corpus="kernelcache",
            analysis="aaaa" if default_analysis != "aa" else default_analysis,
            targets=KERNEL_TARGETS,
            max_functions=default_max_functions,
        )
    ]


def dedupe_cases(cases: list[BinaryCase]) -> list[BinaryCase]:
    seen: set[tuple[str, str]] = set()
    out: list[BinaryCase] = []
    for case in cases:
        key = (str(case.path.resolve()) if case.path.exists() else str(case.path), case.corpus)
        if key in seen:
            continue
        seen.add(key)
        out.append(case)
    out.sort(key=lambda case: (case.corpus, case.name, str(case.path)))
    return out


def build_cases(args: argparse.Namespace) -> list[BinaryCase]:
    cases: list[BinaryCase] = []
    if args.manifest:
        cases.extend(read_manifest(Path(args.manifest), args.analysis, args.max_functions))
    if args.binary:
        cases.extend(direct_binary_cases(args.binary, args.target, args.analysis, args.max_functions))
    if not args.no_repo_fixtures:
        cases.extend(repo_fixture_cases(args.analysis, args.max_functions))
    cases.extend(
        external_corpus_cases(
            "coreutils",
            args.coreutils_dir,
            args.max_binaries_per_corpus,
            args.analysis,
            args.max_functions,
        )
    )
    cases.extend(
        external_corpus_cases(
            "cgc",
            args.cgc_dir,
            args.max_binaries_per_corpus,
            args.analysis,
            args.max_functions,
        )
    )
    cases.extend(
        external_corpus_cases(
            "juliet",
            args.juliet_dir,
            args.max_binaries_per_corpus,
            args.analysis,
            args.max_functions,
        )
    )
    cases.extend(kernel_case(args.kernel, args.analysis, args.max_functions))
    return dedupe_cases(cases)


def discover_functions(
    r2: str,
    case: BinaryCase,
    timeout_s: int,
    env: dict[str, str] | None,
    runner: Runner,
    *,
    with_plugin: bool = True,
) -> tuple[list[dict[str, Any]], CmdResult, str | None]:
    command = f"a:sla >/dev/null; {case.analysis}; aflj" if with_plugin else f"{case.analysis}; aflj"
    result = runner(
        r2,
        case.path,
        command,
        timeout_s,
        env,
    )
    if result.returncode != 0:
        return [], result, "discovery command failed"
    try:
        payload = parse_json_payload(result.stdout)
    except ValueError as exc:
        return [], result, str(exc)
    if not isinstance(payload, list):
        return [], result, "aflj payload is not an array"
    functions: list[dict[str, Any]] = []
    for item in payload:
        if not isinstance(item, dict):
            continue
        name = item.get("name")
        addr = item.get("addr")
        if not isinstance(addr, int):
            addr = item.get("offset")
        if not isinstance(name, str) or not isinstance(addr, int):
            continue
        functions.append(
            {
                "name": name,
                "addr": addr,
                "size": item.get("size") if isinstance(item.get("size"), int) else 0,
                "blocks": item.get("nbbs") if isinstance(item.get("nbbs"), int) else 0,
            }
        )
    functions.sort(key=lambda f: (f["addr"], f["name"]))
    return functions, result, None


def probe_native_pdfj(
    r2: str,
    case: BinaryCase,
    functions: list[dict[str, Any]],
    timeout_s: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    runner: Runner,
) -> dict[str, Any] | None:
    selected = choose_targets(functions, case.targets, 1)
    selected = [target for target in selected if target.get("found", False)]
    if not selected:
        return None
    target = selected[0]
    addr = int(target["addr"])
    result = runner(r2, case.path, f"{case.analysis}; s 0x{addr:x}; pdfj", timeout_s, env)
    out: dict[str, Any] = {
        "target": target.get("name") or target.get("requested"),
        "addr": addr,
        "returncode": result.returncode,
        "elapsed_s": round(result.elapsed_s, 6),
        "runtime_bucket": runtime_bucket(result.elapsed_s),
        "stdout": summarize_text(result.stdout, include_preview=include_sensitive, max_lines=20),
    }
    if result.stderr.strip():
        out["stderr"] = summarize_text(result.stderr, include_preview=include_sensitive, max_lines=20)
    try:
        payload = parse_json_payload(result.stdout)
        out["json_kind"] = type(payload).__name__
        if isinstance(payload, dict):
            ops = payload.get("ops")
            out["op_count"] = len(ops) if isinstance(ops, list) else None
    except ValueError as exc:
        out["json_error"] = str(exc)
    return out


def choose_targets(functions: list[dict[str, Any]], requested: tuple[str, ...], limit: int) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    seen_addrs: set[int] = set()
    by_norm: dict[str, list[dict[str, Any]]] = {}
    for fcn in functions:
        by_norm.setdefault(normalize_symbol(fcn["name"]), []).append(fcn)
    for target in requested:
        norm = normalize_symbol(target)
        candidates = by_norm.get(norm, [])
        if not candidates:
            candidates = [
                fcn
                for fcn in functions
                if normalize_symbol(fcn["name"]).endswith(norm)
                or norm in normalize_symbol(fcn["name"])
            ]
        candidates.sort(key=lambda f: (0 if normalize_symbol(f["name"]) == norm else 1, f["addr"]))
        if not candidates:
            selected.append({"requested": target, "found": False})
            continue
        fcn = candidates[0]
        if fcn["addr"] in seen_addrs:
            continue
        seen_addrs.add(fcn["addr"])
        selected.append({**fcn, "requested": target, "found": True})
    if selected:
        return selected

    top = sorted(functions, key=lambda f: (-int(f.get("size") or 0), -int(f.get("blocks") or 0), f["addr"], f["name"]))
    for fcn in top[: max(0, limit)]:
        selected.append({**fcn, "requested": fcn["name"], "found": True})
    selected.sort(key=lambda f: (not f.get("found", False), f.get("addr", 0), f.get("name", "")))
    return selected


def command_summary(name: str, result: CmdResult, include_sensitive: bool) -> dict[str, Any]:
    entry: dict[str, Any] = {
        "returncode": result.returncode,
        "elapsed_s": round(result.elapsed_s, 6),
        "runtime_bucket": runtime_bucket(result.elapsed_s),
        "stdout": summarize_text(result.stdout, include_preview=include_sensitive),
    }
    if result.stderr.strip():
        entry["stderr"] = summarize_text(result.stderr, include_preview=include_sensitive)
    if name in ("types", "profile"):
        try:
            payload = parse_json_payload(result.stdout)
            entry["json_kind"] = type(payload).__name__
            if name == "types" and isinstance(payload, dict):
                params = payload.get("params")
                mutations = payload.get("mutation_plan", {}).get("mutations") if isinstance(payload.get("mutation_plan"), dict) else None
                entry["type_metrics"] = {
                    "ret_type": payload.get("ret_type") if isinstance(payload.get("ret_type"), str) else None,
                    "param_count": len(params) if isinstance(params, list) else None,
                    "mutation_count": len(mutations) if isinstance(mutations, list) else None,
                    **generic_type_metrics(payload),
                }
            if name == "profile" and isinstance(payload, dict):
                entry["profile_metrics"] = {
                    "count": payload.get("count") if isinstance(payload.get("count"), int) else None,
                    "cache_hits": payload.get("decompile_cache", {}).get("hits") if isinstance(payload.get("decompile_cache"), dict) else None,
                    "cache_misses": payload.get("decompile_cache", {}).get("misses") if isinstance(payload.get("decompile_cache"), dict) else None,
                }
        except ValueError as exc:
            entry["json_error"] = str(exc)
    if name in ("decompile_sla", "decompile_pdd"):
        quality = decompile_quality(result.stdout)
        entry["decompile_quality"] = quality
        if quality["fallback_marker"] is not None:
            entry["fallback_marker"] = quality["fallback_marker"]
        entry["residual_markers"] = quality["residual_markers"]
        entry["empty"] = quality["empty"]
    return entry


def collect_target(
    r2: str,
    case: BinaryCase,
    target: dict[str, Any],
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    runner: Runner,
) -> dict[str, Any]:
    if not target.get("found", True):
        return dict(target)
    addr = int(target["addr"])
    prefix = f"a:sla >/dev/null; {case.analysis}; s 0x{addr:x}; af"
    commands = {
        "decompile_sla": "a:sla.dec",
        "decompile_pdd": "pdd",
        "types": "a:sla.debug.types",
        "profile": "a:sla.debug.profilej",
    }
    out: dict[str, Any] = dict(target)
    out["commands"] = {}
    repeat_count = max(1, repeat)
    for name, command in commands.items():
        runs = [
            runner(r2, case.path, f"{prefix}; {command}", timeout_s, env)
            for _ in range(repeat_count if name in ("decompile_sla", "types") else 1)
        ]
        entry = command_summary(name, runs[0], include_sensitive)
        if len(runs) > 1:
            hashes = [hashlib.sha256(run.stdout.encode("utf-8", "replace")).hexdigest() for run in runs]
            entry["repeat"] = {
                "count": len(runs),
                "stable": len(set(hashes)) == 1,
                "hashes": hashes,
            }
        out["commands"][name] = entry
    return out


def collect_failures(case_result: dict[str, Any]) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    native = case_result.get("native_discovery", {})
    if native:
        repro = native.get("repro") or "aa; aflj"
        if native.get("returncode") != 0:
            failures.append(
                {
                    "kind": "radare2_candidate",
                    "reason": "native discovery command failed",
                    "command": "aflj",
                    "repro": repro,
                }
            )
        if native.get("error"):
            failures.append(
                {
                    "kind": "radare2_candidate",
                    "reason": f"native discovery parse: {native.get('error')}",
                    "command": "aflj",
                    "repro": repro,
                }
            )
        if native.get("function_count") == 0:
            failures.append(
                {
                    "kind": "radare2_candidate",
                    "reason": "native discovery found zero functions",
                    "command": "aflj",
                    "repro": repro,
                }
            )
    native_pdfj = case_result.get("native_pdfj_probe", {})
    if native_pdfj:
        if native_pdfj.get("returncode") != 0 or native_pdfj.get("json_error"):
            failures.append(
                {
                    "kind": "radare2_candidate",
                    "reason": native_pdfj.get("json_error") or "native pdfj command failed",
                    "command": "pdfj",
                    "target": native_pdfj.get("target"),
                    "repro": f"{case_result.get('analysis', 'aa')}; s 0x{int(native_pdfj.get('addr', 0)):x}; pdfj",
                }
            )
    discovery = case_result.get("discovery", {})
    if discovery.get("returncode") != 0:
        failures.append({"kind": "discovery_return", "command": "aflj"})
    if discovery.get("error"):
        failures.append({"kind": "discovery_parse", "error": discovery.get("error")})
    if discovery.get("function_count") == 0:
        failures.append({"kind": "zero_functions", "command": "aflj"})
    for target in case_result.get("targets", []):
        target_name = target.get("name") or target.get("requested")
        if not target.get("found", True):
            failures.append({"kind": "missing_target", "target": target_name})
            continue
        for command, result in target.get("commands", {}).items():
            if result.get("returncode") != 0:
                failures.append({"kind": "command_return", "target": target_name, "command": command})
            if result.get("json_error"):
                failures.append({"kind": "json_parse", "target": target_name, "command": command})
            if result.get("empty") is True:
                failures.append({"kind": "empty_decompile", "target": target_name, "command": command})
            if result.get("fallback_marker"):
                failures.append({"kind": "decompiler_fallback", "target": target_name, "command": command})
            repeat = result.get("repeat")
            if isinstance(repeat, dict) and repeat.get("stable") is False:
                failures.append({"kind": "nondeterministic_output", "target": target_name, "command": command})
    failures.sort(key=lambda item: (item.get("kind", ""), item.get("target", ""), item.get("command", "")))
    return failures


def score_case(case_result: dict[str, Any]) -> int:
    penalty_by_kind = {
        "discovery_return": 25,
        "discovery_parse": 20,
        "zero_functions": 20,
        "missing_target": 15,
        "command_return": 10,
        "empty_decompile": 10,
        "decompiler_fallback": 10,
        "json_parse": 5,
        "nondeterministic_output": 10,
        "radare2_candidate": 8,
    }
    score = 100
    for failure in case_result.get("failures", []):
        score -= penalty_by_kind.get(failure.get("kind"), 3)
    residuals = 0
    for target in case_result.get("targets", []):
        for result in target.get("commands", {}).values():
            residuals += int(result.get("residual_markers") or 0)
    score -= min(15, residuals)
    return max(0, min(100, score))


def run_case(
    r2: str,
    case: BinaryCase,
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    runner: Runner = run_r2,
) -> dict[str, Any]:
    started = time.perf_counter()
    case_out: dict[str, Any] = {
        "name": case.name,
        "corpus": case.corpus,
        "binary": display_path(case.path, include_sensitive),
        "analysis": case.analysis,
        "requested_targets": list(case.targets),
    }
    if not case.path.exists():
        case_out["discovery"] = {
            "returncode": 127,
            "function_count": 0,
            "error": "binary does not exist",
        }
        case_out["targets"] = []
        case_out["elapsed_s"] = round(time.perf_counter() - started, 6)
        case_out["failures"] = collect_failures(case_out)
        case_out["score"] = score_case(case_out)
        return case_out

    native_functions, native_discovery, native_error = discover_functions(
        r2,
        case,
        timeout_s,
        env,
        runner,
        with_plugin=False,
    )
    native_probe = probe_native_pdfj(
        r2,
        case,
        native_functions,
        timeout_s,
        include_sensitive,
        env,
        runner,
    )
    case_out["native_discovery"] = {
        "returncode": native_discovery.returncode,
        "elapsed_s": round(native_discovery.elapsed_s, 6),
        "runtime_bucket": runtime_bucket(native_discovery.elapsed_s),
        "function_count": len(native_functions),
        "stdout": summarize_text(native_discovery.stdout, include_preview=include_sensitive, max_lines=20),
        "repro": f"{case.analysis}; aflj",
    }
    if native_discovery.stderr.strip():
        case_out["native_discovery"]["stderr"] = summarize_text(
            native_discovery.stderr, include_preview=include_sensitive, max_lines=20
        )
    if native_error:
        case_out["native_discovery"]["error"] = native_error
    if native_probe is not None:
        case_out["native_pdfj_probe"] = native_probe

    functions, discovery, discovery_error = discover_functions(r2, case, timeout_s, env, runner)
    case_out["discovery"] = {
        "returncode": discovery.returncode,
        "elapsed_s": round(discovery.elapsed_s, 6),
        "runtime_bucket": runtime_bucket(discovery.elapsed_s),
        "function_count": len(functions),
        "stdout": summarize_text(discovery.stdout, include_preview=include_sensitive, max_lines=20),
    }
    if discovery.stderr.strip():
        case_out["discovery"]["stderr"] = summarize_text(
            discovery.stderr, include_preview=include_sensitive, max_lines=20
        )
    if discovery_error:
        case_out["discovery"]["error"] = discovery_error
    selected = choose_targets(functions, case.targets, case.max_functions)
    case_out["targets"] = [
        collect_target(
            r2,
            case,
            target,
            timeout_s,
            repeat,
            include_sensitive,
            env,
            runner,
        )
        for target in selected
    ]
    case_out["elapsed_s"] = round(time.perf_counter() - started, 6)
    case_out["failures"] = collect_failures(case_out)
    case_out["score"] = score_case(case_out)
    return case_out


def aggregate(cases: list[dict[str, Any]]) -> dict[str, Any]:
    failures_by_kind: dict[str, int] = {}
    slow_commands: list[dict[str, Any]] = []
    runtime_buckets: dict[str, int] = {}
    decompile_quality_buckets: dict[str, int] = {}
    generic_arg_total = 0
    generic_type_total = 0
    radare2_candidates = 0
    total_targets = 0
    for case in cases:
        for failure in case.get("failures", []):
            kind = str(failure.get("kind", "unknown"))
            failures_by_kind[kind] = failures_by_kind.get(kind, 0) + 1
            if kind == "radare2_candidate":
                radare2_candidates += 1
        for native_key in ("native_discovery", "native_pdfj_probe"):
            native_result = case.get(native_key)
            if isinstance(native_result, dict):
                bucket = str(native_result.get("runtime_bucket") or "unknown")
                runtime_buckets[bucket] = runtime_buckets.get(bucket, 0) + 1
        for target in case.get("targets", []):
            if target.get("found", True):
                total_targets += 1
            for command, result in target.get("commands", {}).items():
                bucket = str(result.get("runtime_bucket") or "unknown")
                runtime_buckets[bucket] = runtime_buckets.get(bucket, 0) + 1
                quality = result.get("decompile_quality")
                if isinstance(quality, dict):
                    classification = str(quality.get("classification") or "unknown")
                    decompile_quality_buckets[classification] = (
                        decompile_quality_buckets.get(classification, 0) + 1
                    )
                type_metrics = result.get("type_metrics")
                if isinstance(type_metrics, dict):
                    generic_arg_total += int(type_metrics.get("generic_arg_count") or 0)
                    generic_type_total += int(type_metrics.get("generic_type_count") or 0)
                slow_commands.append(
                    {
                        "case": case.get("name"),
                        "corpus": case.get("corpus"),
                        "target": target.get("name") or target.get("requested"),
                        "command": command,
                        "elapsed_s": result.get("elapsed_s", 0),
                    }
                )
    slow_commands.sort(key=lambda item: (-float(item["elapsed_s"]), item["corpus"], item["case"], item["target"], item["command"]))
    scores = [int(case.get("score", 0)) for case in cases]
    failures_sorted = dict(sorted(failures_by_kind.items()))
    return {
        "case_count": len(cases),
        "target_count": total_targets,
        "average_score": round(sum(scores) / len(scores), 2) if scores else 0.0,
        "min_score": min(scores) if scores else 0,
        "failures_by_kind": failures_sorted,
        "quality": {
            "decompile": dict(sorted(decompile_quality_buckets.items())),
            "runtime_buckets": dict(sorted(runtime_buckets.items())),
            "generic_arg_total": generic_arg_total,
            "generic_type_total": generic_type_total,
            "radare2_candidate_count": radare2_candidates,
        },
        "slowest_commands": slow_commands[:20],
    }


def write_report(path: Path, report: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    cases = build_cases(args)
    env = build_r2_env(args.r2, args.plugin_dir, Path(args.tmpdir) if args.tmpdir else None)
    results = [
        run_case(
            args.r2,
            case,
            args.timeout,
            args.repeat,
            args.include_sensitive,
            env,
        )
        for case in cases
    ]
    report = {
        "schema": SCHEMA_VERSION,
        "status": "ok" if all(not result.get("failures") for result in results) else "issues",
        "r2": args.r2,
        "analysis": args.analysis,
        "repeat": max(1, args.repeat),
        "inputs": {
            "manifest": args.manifest or None,
            "repo_fixtures": not args.no_repo_fixtures,
            "coreutils_dir": display_path(Path(args.coreutils_dir), args.include_sensitive) if args.coreutils_dir else None,
            "cgc_dir": display_path(Path(args.cgc_dir), args.include_sensitive) if args.cgc_dir else None,
            "juliet_dir": display_path(Path(args.juliet_dir), args.include_sensitive) if args.juliet_dir else None,
            "kernel": display_path(Path(args.kernel), args.include_sensitive) if args.kernel else None,
        },
        "summary": aggregate(results),
        "cases": results,
    }
    if not results:
        report["status"] = "skipped"
        report["reason"] = "no benchmark binaries found"
    out_path = Path(args.out)
    write_report(out_path, report)
    print(
        "reversing benchmark "
        f"{report['status']}; cases={report['summary']['case_count']} "
        f"avg_score={report['summary']['average_score']} wrote {out_path}"
    )
    if args.strict and report["status"] == "issues":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
