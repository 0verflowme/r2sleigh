#!/usr/bin/env python3
"""Deterministic reversing benchmark harness for r2sleigh.

The harness does not download or commit corpora. It consumes local binaries from
repo fixtures, optional public-corpus directories, a manifest, and an optional
kernelcache path, then emits a sorted JSON report that can drive product work.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import copy
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Optional, TypeVar, cast


SCHEMA_VERSION = 8
DEFAULT_TMPDIR = "/tmp/r2sleigh-reversing-benchmark-tmp"
DEFAULT_OUT = "/tmp/r2sleigh-reversing-benchmark.json"
DEFAULT_MAX_BINARIES_PER_CORPUS = 8
DEFAULT_MAX_FUNCTIONS = 6
DEFAULT_TIMEOUT = 180
DEFAULT_ANALYSIS = "aaa"
DEFAULT_JOBS = max(1, os.cpu_count() or 1)
BATCH_SENTINEL = "__R2SLEIGH_BENCH_SECTION__"
BATCH_SECTION_COMPLETED = "completed"
BATCH_SECTION_STARTED_TIMEOUT = "started_timeout"
BATCH_SECTION_STARTED_FAILED = "started_failed"
BATCH_SECTION_NOT_REACHED = "not_reached"
BATCH_SECTION_SETUP_FAILED = "setup_failed"
INCOMPLETE_SECTION_STATUSES = {
    BATCH_SECTION_NOT_REACHED,
    BATCH_SECTION_SETUP_FAILED,
}
DECOMPILER_FALLBACK_MARKERS = (
    "r2dec fallback:",
    "r2dec: decompilation panicked",
    "r2dec: failed to spawn",
    "skipped decompilation",
    "r2pm -ci r2dec",
    "r2pm -ci r2ghidra",
    "install the plugin with r2pm",
)
RESIDUAL_MARKERS = ("budget", "residual", "largecfg", "large cfg", "timeout")
RESIDUAL_MARKER_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:budget|residual|largecfg|large cfg|timeout)(?![A-Za-z0-9_])",
    re.IGNORECASE,
)
TEMP_ARTIFACT_RE = re.compile(
    r"\b(?:tmp[:_][A-Za-z0-9_:.]+|unique[:_][A-Za-z0-9_:.]+|unk_[A-Za-z0-9_]+|"
    r"(?:SP|FP|LR|PC|X[0-9]+|R[0-9A-Z]+)_[0-9]+|"
    r"(?:e?(?:ax|bx|cx|dx|si|di|bp|sp)|r(?:[0-9]+|ax|bx|cx|dx|si|di|bp|sp))[bwdq]?_[0-9]+)\b"
)
BARE_REGISTER_ARTIFACT_RE = re.compile(
    r"\b(?:RAX|RBX|RCX|RDX|RSI|RDI|RBP|RSP|RIP|"
    r"EAX|EBX|ECX|EDX|ESI|EDI|EBP|ESP|X[0-9]+|W[0-9]+|R[0-9]+)\b"
)
GENERIC_NAME_RE = re.compile(r"^(?:arg|param|var)[._]?[0-9]+$", re.IGNORECASE)
GENERIC_TYPE_RE = re.compile(
    r"(?:\b(?:unknown|undefined|unk|uint(?:32|64)_t|int(?:32|64)_t)\b|void\s*\*)",
    re.IGNORECASE,
)
UNSAMPLED_CODE_NAME_RE = re.compile(
    r"^(?:fcn|sub)\.[0-9a-f]+$",
    re.IGNORECASE,
)
ADDRESS_OF_SCALAR_SMELL_RE = re.compile(
    r"(?:=\s*&[A-Za-z_][A-Za-z0-9_]*\b|[+\-*/]\s*&[A-Za-z_][A-Za-z0-9_]*\b|"
    r"&[A-Za-z_][A-Za-z0-9_]*\s*[+\-*/])"
)
LOCAL_STACK_PLACEHOLDER_RE = re.compile(r"\b&?local_[0-9a-f]+\b", re.IGNORECASE)
STACK_ADDRESS_LEAK_RE = re.compile(r"&(?:local_[0-9a-f]+|var_[0-9a-f]+h?|stack_[0-9a-f]+)\b", re.IGNORECASE)
CAST_EXPR_RE = re.compile(
    r"\((?:const\s+|volatile\s+)?"
    r"(?:(?:u?int(?:8|16|32|64)_t|size_t|ssize_t|uintptr_t|intptr_t|"
    r"char|short|int|long|bool|void)"
    r"|(?:struct\s+)?[A-Za-z_][A-Za-z0-9_]*)"
    r"(?:\s*\*+)?\s*\)(?=\s*(?:[A-Za-z_0-9*&(]))"
)
POINTER_CAST_RE = re.compile(
    r"\((?:const\s+|volatile\s+)?"
    r"(?:(?:u?int(?:8|16|32|64)_t|size_t|ssize_t|uintptr_t|intptr_t|"
    r"char|short|int|long|bool|void)"
    r"|(?:struct\s+)?[A-Za-z_][A-Za-z0-9_]*)"
    r"\s*\*+\s*\)(?=\s*(?:[A-Za-z_0-9*&(]))"
)
CONTROL_FLOW_NOISE_RE = re.compile(r"\b(?:goto\s+[A-Za-z_][A-Za-z0-9_]*|while\s*\(\s*(?:1|true)\s*\))", re.IGNORECASE)
LOOP_OR_SWITCH_RE = re.compile(r"\b(?:for|while|switch)\s*\(", re.IGNORECASE)
ORPHAN_BREAK_RE = re.compile(r"^\s*break;\s*(?://.*)?$", re.MULTILINE)
CALL_READABILITY_NOISE_RE = re.compile(
    r"\b(?:call_[0-9a-f]+|sym\.imp\.|fcn\.[0-9a-f]+)\b", re.IGNORECASE
)
SUMMARY_PSEUDO_CALL_RE = re.compile(
    r"\b(?:scan_[A-Za-z0-9_]*_summary|walk_[A-Za-z0-9_]*_summary|"
    r"compute_[A-Za-z0-9_]*_transform|[A-Za-z0-9_]+_fold_summary|"
    r"parse_[A-Za-z0-9_]*_summary)\s*\("
)
RETURN_IDENTIFIER_RE = re.compile(r"\breturn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*;")
UNRESOLVED_FCN_RE = re.compile(r"\bfcn\.[0-9a-f]+\b", re.IGNORECASE)
ARGN_LEAK_RE = re.compile(r"\barg[._]?[0-9]+\b", re.IGNORECASE)
RAW_TEMP_STACK_LEAK_RE = re.compile(
    r"\b(?:tmp[:_][A-Za-z0-9_:.]+|unique[:_][A-Za-z0-9_:.]+|"
    r"stack_[0-9a-f]+|var_[0-9a-f]+h?|local_[0-9a-f]+)\b",
    re.IGNORECASE,
)
FAKE_WHILE_BREAK_RE = re.compile(
    r"\bwhile\s*\([^)]*\)\s*\{\s*break;\s*\}",
    re.IGNORECASE | re.DOTALL,
)
EMPTY_LOOP_BODY_RE = re.compile(
    r"\bdo\s*\{\s*\}\s*while\s*\([^)]*\)\s*;|"
    r"\b(?:while|for)\s*\([^)]*\)\s*\{\s*\}",
    re.IGNORECASE | re.DOTALL,
)
FUNCTION_HEADER_RE = re.compile(
    r"^\s*(?P<ret>(?:const\s+|volatile\s+|struct\s+)*[A-Za-z_][A-Za-z0-9_]*"
    r"(?:\s+[*A-Za-z_][A-Za-z0-9_]*)*(?:\s*\*+)?)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.]*)\s*\((?P<params>[^()]*)\)\s*(?:\{|$)",
    re.MULTILINE,
)
SYNTHETIC_TYPE_LEAK_RE = re.compile(
    r"\b(?:sla_struct_[A-Za-z0-9_]+|struct\s+local_[A-Za-z0-9_]+|undefined(?:[0-9]+)?|unk(?:nown)?_t)\b",
    re.IGNORECASE,
)
BLOCK_COMMENT_RE = re.compile(r"/\*.*?\*/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"//.*?$", re.MULTILINE)
HEADER_PARAM_RE = re.compile(r"^[^{;]*\((?P<params>[^()]*)\)")
LOCAL_DECL_RE = re.compile(
    r"^\s*(?:const\s+)?(?:u?int(?:8|16|32|64)_t|char|short|int|long|bool|size_t|ssize_t|void)\s+"
    r"\*?\s*(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*(?:[=;,\[])"
)
TARGET_COMMAND_DEFS: dict[str, str] = {
    "decompile_sla": "a:sla.dec",
    "decompile_pdd": "pdd",
    "decompile_pdg": "pdg",
    "types": "a:sla.debug.types",
    "profile": "a:sla.debug.profilej",
}
DEFAULT_TARGET_COMMANDS = ("decompile_sla", "decompile_pdd", "types", "profile")
TIER1_TARGET_COMMANDS = ("decompile_sla", "types", "profile")
DECOMPILE_COMMAND_PREFIX = "decompile_"
DECOMPILE_REPEAT_COMMANDS = ("decompile_sla", "decompile_pdg", "types")
BASELINE_COMMANDS = {"decompile_pdg"}
QUALITY_RANK = {"empty": 0, "fallback": 1, "residual": 2, "structured": 3}
QUALITY_GATE_FAILURES = {
    "argn_leak",
    "comment_only_decompile",
    "decompile_header_return_mismatch",
    "decompile_header_signature_mismatch",
    "empty_loop_body",
    "fake_while_break_wrapper",
    "missing_return_nonvoid",
    "summary_pseudo_call",
    "undefined_identifier_return",
    "unresolved_fcn_or_temp_stack_leak",
}
GOLD_ORACLE_FAILURE = "source_oracle_failure"
FAILURE_OWNER = {
    "argn_leak": "r2types",
    "comment_only_decompile": "r2dec",
    "command_return": "r2plugin",
    "decompile_header_return_mismatch": "r2types",
    "decompile_header_signature_mismatch": "r2types",
    "decompiler_fallback": "r2dec",
    "discovery_parse": "radare2",
    "discovery_return": "radare2",
    "empty_decompile": "r2dec",
    "empty_loop_body": "r2dec",
    "fake_while_break_wrapper": "r2dec",
    "json_parse": "r2plugin",
    "missing_return_nonvoid": "r2dec",
    "source_oracle_failure": "unknown",
    "summary_pseudo_call": "r2dec",
    "undefined_identifier_return": "r2dec",
    "missing_debug_target_alias": "radare2",
    "missing_symbol_target_alias": "radare2",
    "missing_target": "radare2",
    "nondeterministic_output": "r2engine",
    "radare2_candidate": "radare2",
    "timeout": "r2engine",
    "unresolved_fcn_or_temp_stack_leak": "r2ssa",
    "zero_functions": "radare2",
}
OWNER_ACTIONS = {
    "radare2": "extend typed radare2 collectors, discovery aliases, or native analysis metadata",
    "r2ssa": "push missing CFG, def-use, stack, or callsite facts into prepared SSA facts",
    "r2sym": "add structural semantic evidence, summaries, or explicit refusal policy",
    "r2types": "project canonical semantic evidence into FunctionTypeFacts and writeback facts",
    "r2engine": "fix route selection, cache reuse, budget, or determinism policy",
    "r2dec": "render only canonical facts and improve structuring from summary-backed evidence",
    "r2plugin": "fix command dispatch, FFI, or typed session plumbing without adding policy",
    "unknown": "classify the failure into a canonical owner before implementing a fix",
}
CACHE_COUNTER_FIELDS = ("hits", "misses", "lookups", "insertions", "evictions")
TARGET_ALIAS_PREFIXES = {"sym", "dbg"}
CACHE_METRIC_KEYS = (
    "decompile_cache",
    "summary_cache",
    "semantic_summary_cache",
    "interproc_summary_cache",
    "type_summary_cache",
    "cache",
)
FAST_PATH_BOOL_FIELDS = (
    "fast_path",
    "fastpath",
    "summary_fast_path",
    "cache_fast_path",
    "cache_hit",
    "summary_hit",
)
FAST_PATH_COUNTER_FIELDS = (
    "fast_path_hits",
    "fast_path_misses",
    "summary_hits",
    "summary_misses",
    "target_summary_rank_hits",
    "target_pruned_summary_contradiction",
)
SEMANTIC_SUMMARY_COUNT_FIELDS = (
    "closure_functions",
    "helper_functions",
    "derived_summaries",
    "summary_attempted",
    "summary_budget_exhausted",
    "summary_scc_count",
    "native_region_summary_count",
    "native_worker_summary_count",
    "region_count",
    "memory_fact_count",
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
COREUTILS_FOCUSED_TARGETS = (
    ("dd", "dbg.xstrtoumax"),
    ("printf", "sym.printf_fetchargs"),
    ("uniq", "dbg.readlinebuffer_delim"),
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
T = TypeVar("T")
U = TypeVar("U")


class LimitedRunner:
    """Bound concurrent radare2 subprocesses across nested benchmark workers."""

    def __init__(self, runner: Runner, jobs: int) -> None:
        self._runner = runner
        self._semaphore = threading.BoundedSemaphore(max(1, jobs))

    def __call__(
        self,
        r2: str,
        binary: Path,
        cmd: str,
        timeout_s: int,
        env: dict[str, str] | None,
    ) -> CmdResult:
        with self._semaphore:
            return self._runner(r2, binary, cmd, timeout_s, env)


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


def default_baseline_plugin_dirs() -> list[str]:
    value = os.environ.get("R2SLEIGH_BASELINE_PLUGIN_DIR", "").strip()
    if not value:
        return []
    return [part for part in value.split(os.pathsep) if part]


def positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"expected positive integer, got {value!r}") from exc
    if parsed < 1:
        raise argparse.ArgumentTypeError(f"expected positive integer, got {value!r}")
    return parsed


def nonnegative_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"expected non-negative integer, got {value!r}") from exc
    if parsed < 0:
        raise argparse.ArgumentTypeError(f"expected non-negative integer, got {value!r}")
    return parsed


def default_jobs() -> int:
    raw = os.environ.get("R2SLEIGH_BENCH_JOBS", "").strip()
    if not raw:
        return DEFAULT_JOBS
    try:
        return positive_int(raw)
    except argparse.ArgumentTypeError:
        return DEFAULT_JOBS


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run deterministic r2sleigh reversing benchmarks over local corpora."
    )
    parser.add_argument(
        "--preset",
        choices=("smoke", "tier1", "full"),
        default="",
        help="benchmark preset; explicit CLI options still override defaults",
    )
    parser.add_argument(
        "--compare",
        nargs=2,
        metavar=("BEFORE", "AFTER"),
        help="compare two benchmark JSON reports and print a compact JSON delta",
    )
    parser.add_argument("--r2", default=default_r2_path(), help="radare2 executable path")
    parser.add_argument(
        "--plugin-dir",
        default=default_plugin_dir(),
        help="radare2 plugin directory for benchmark runs",
    )
    parser.add_argument(
        "--baseline-plugin-dir",
        action="append",
        default=default_baseline_plugin_dirs(),
        help="additional radare2 plugin directory for baseline tools such as r2ghidra/pdg; may be repeated",
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
        "--gold-manifest",
        default="",
        help=(
            "optional source-gold oracle manifest; matching expectations are "
            "checked against command output and reported separately from smell metrics"
        ),
    )
    parser.add_argument(
        "--manifest-only",
        action="store_true",
        help="run only manifest/direct binary inputs; suppress repo fixtures and corpus auto-discovery",
    )
    parser.add_argument(
        "--override-manifest-max-functions",
        action="store_true",
        help="use --max-functions for manifest cases even when the manifest pins per-binary limits",
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
        "--focused-coreutils",
        action="store_true",
        help="run focused Coreutils benchmark targets for known hot functions",
    )
    parser.add_argument(
        "--isolate-commands",
        action="store_true",
        help="run each target command in a separate radare2 process",
    )
    parser.add_argument(
        "--batch-target-size",
        type=nonnegative_int,
        default=0,
        help="maximum targets per batched radare2 process; 0 keeps all selected targets in one batch",
    )
    parser.add_argument(
        "--commands",
        default="",
        help=(
            "comma-separated per-target commands to run; choices: "
            + ",".join(TARGET_COMMAND_DEFS)
        ),
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="reuse completed cases from --out when the benchmark configuration matches",
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
        "--cache-probe",
        action="store_true",
        help=(
            "run a repeated decompile/types/profile sequence to measure same-session "
            "engine artifact and render cache reuse"
        ),
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help="radare2 subprocess timeout in seconds",
    )
    parser.add_argument(
        "--jobs",
        type=positive_int,
        default=default_jobs(),
        help="maximum concurrent radare2 subprocesses",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="return non-zero when benchmark failures are detected",
    )
    parser.add_argument(
        "--closure-gate",
        action="store_true",
        help=(
            "apply the default gold-closure quality gate: strict mode, no hard failures, "
            "no residuals/generic type debt, average score >= 99.5, and setup/command "
            "ratio <= 2.0 unless thresholds are overridden"
        ),
    )
    parser.add_argument(
        "--max-hard-failures",
        type=nonnegative_int,
        default=None,
        help="strict quality gate: maximum allowed hard benchmark failures",
    )
    parser.add_argument(
        "--max-residual-decompile",
        type=nonnegative_int,
        default=None,
        help="strict quality gate: maximum allowed residual decompile command count",
    )
    parser.add_argument(
        "--max-generic-args",
        type=nonnegative_int,
        default=None,
        help="strict quality gate: maximum allowed generic argument-name count",
    )
    parser.add_argument(
        "--max-generic-types",
        type=nonnegative_int,
        default=None,
        help="strict quality gate: maximum allowed generic type count",
    )
    parser.add_argument(
        "--min-average-score",
        type=float,
        default=None,
        help="strict quality gate: minimum allowed average benchmark score",
    )
    parser.add_argument(
        "--max-setup-command-ratio",
        type=float,
        default=None,
        help="strict performance gate: maximum allowed setup_s / command_s ratio",
    )
    parser.add_argument(
        "--require-pdg-comparison",
        action="store_true",
        help="strict comparison gate: fail when no successful decompile_sla/decompile_pdg common targets exist",
    )
    parser.add_argument(
        "--max-pdg-quality-wins",
        type=nonnegative_int,
        default=None,
        help="strict comparison gate: maximum targets where pdg beats decompile_sla on quality",
    )
    parser.add_argument(
        "--max-pdg-perf-wins",
        type=nonnegative_int,
        default=None,
        help="strict comparison gate: maximum targets where pdg beats decompile_sla on elapsed time",
    )
    parser.add_argument(
        "--max-pdg-quality-then-perf-wins",
        type=nonnegative_int,
        default=None,
        help=(
            "strict comparison gate: maximum targets where pdg wins a lexicographic "
            "quality-then-elapsed comparison against decompile_sla"
        ),
    )
    parser.add_argument(
        "--max-gold-failures",
        type=nonnegative_int,
        default=None,
        help="strict quality gate: maximum allowed source-gold oracle failures",
    )
    parser.add_argument(
        "--require-gold",
        action="store_true",
        help="strict quality gate: fail when no source-gold expectations were exercised",
    )
    parser.add_argument(
        "--include-sensitive",
        action="store_true",
        help="include local paths and output previews in the report",
    )
    args = parser.parse_args()
    apply_preset_defaults(args)
    return args


def apply_preset_defaults(args: argparse.Namespace) -> None:
    if args.preset == "smoke":
        if args.max_binaries_per_corpus == DEFAULT_MAX_BINARIES_PER_CORPUS:
            args.max_binaries_per_corpus = 0
        if args.max_functions == DEFAULT_MAX_FUNCTIONS:
            args.max_functions = 2
        if args.timeout == DEFAULT_TIMEOUT:
            args.timeout = 90
    elif args.preset == "tier1":
        if not args.focused_coreutils:
            args.focused_coreutils = True
        if args.max_functions == DEFAULT_MAX_FUNCTIONS:
            args.max_functions = 12
        if args.timeout == DEFAULT_TIMEOUT:
            args.timeout = 120
        if not args.commands:
            args.commands = ",".join(TIER1_TARGET_COMMANDS)
    elif args.preset == "full":
        pass
    if getattr(args, "cache_probe", False):
        args.repeat = max(2, int(getattr(args, "repeat", 1) or 1))
        if not args.commands:
            args.commands = ",".join(TIER1_TARGET_COMMANDS)
    if getattr(args, "closure_gate", False):
        args.strict = True
        if args.max_hard_failures is None:
            args.max_hard_failures = 0
        if args.max_residual_decompile is None:
            args.max_residual_decompile = 0
        if args.max_generic_args is None:
            args.max_generic_args = 0
        if args.max_generic_types is None:
            args.max_generic_types = 0
        if args.min_average_score is None:
            args.min_average_score = 99.5
        if args.max_setup_command_ratio is None:
            args.max_setup_command_ratio = 2.0
        if getattr(args, "max_gold_failures", None) is None:
            args.max_gold_failures = 0
        try:
            command_names = set(parse_command_filter(args.commands))
        except ValueError:
            command_names = set()
        if "decompile_pdg" in command_names:
            args.require_pdg_comparison = True
            if getattr(args, "max_pdg_quality_wins", None) is None:
                args.max_pdg_quality_wins = 0
            if getattr(args, "max_pdg_quality_then_perf_wins", None) is None:
                args.max_pdg_quality_then_perf_wins = 0

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


def target_alias_prefix(name: Any) -> str | None:
    if not isinstance(name, str):
        return None
    prefix, sep, _rest = name.partition(".")
    normalized = prefix.lower()
    return normalized if sep and normalized in TARGET_ALIAS_PREFIXES else None


def target_alias_diagnostic(requested: str, matched: str) -> dict[str, Any] | None:
    requested_prefix = target_alias_prefix(requested)
    matched_prefix = target_alias_prefix(matched)
    if (
        requested_prefix is None
        or matched_prefix is None
        or requested_prefix == matched_prefix
        or normalize_symbol(requested) != normalize_symbol(matched)
    ):
        return None
    if requested_prefix == "dbg" and matched_prefix == "sym":
        kind = "missing_debug_target_alias"
    elif requested_prefix == "sym" and matched_prefix == "dbg":
        kind = "missing_symbol_target_alias"
    else:
        kind = "missing_symbol_debug_target_alias"
    return {
        "kind": kind,
        "requested": requested,
        "matched": matched,
        "requested_prefix": requested_prefix,
        "matched_prefix": matched_prefix,
    }


def target_candidate_rank(requested: str, fcn: dict[str, Any]) -> tuple[int, int, str]:
    name = str(fcn.get("name") or "")
    requested_norm = normalize_symbol(requested)
    candidate_norm = normalize_symbol(name)
    requested_prefix = target_alias_prefix(requested)
    candidate_prefix = target_alias_prefix(name)
    if name.lower() == requested.lower():
        rank = 0
    elif requested_prefix is not None and requested_prefix == candidate_prefix and requested_norm == candidate_norm:
        rank = 1
    elif requested_norm == candidate_norm:
        rank = 2
    else:
        rank = 3
    return rank, int(fcn.get("addr") or 0), name


def annotate_target_match(target: str, fcn: dict[str, Any]) -> dict[str, Any]:
    matched = str(fcn.get("name") or "")
    out = {**fcn, "requested": target, "found": True}
    alias = target_alias_diagnostic(target, matched)
    if alias:
        out["target_match"] = "symbol_debug_alias"
        out["target_alias"] = alias
    elif matched.lower() == target.lower():
        out["target_match"] = "exact"
    elif normalize_symbol(matched) == normalize_symbol(target):
        out["target_match"] = "normalized"
    else:
        out["target_match"] = "fuzzy"
    return out


def target_family(name: str | None) -> str:
    normalized = normalize_symbol(name or "")
    base = normalized.split(".")[0]
    if not base:
        return "unknown"
    if base in {"digest_file", "shaxxx_stream"}:
        return "digest_stream"
    if base in {"binop", "binary_operator", "unary_operator", "or", "three_arguments"}:
        return "expression_eval"
    if base in {
        "argmatch",
        "argmatch_exact",
        "argmatch_invalid",
        "argmatch_valid",
        "xargmatch_internal",
    }:
        return "argmatch"
    if base in {"write_counts", "print_xfer_stats"}:
        return "counter_output"
    if base in {"verror_at_line", "error_at_line"}:
        return "diagnostic_wrapper"
    if base in {
        "quotearg_buffer_restyled",
        "quotearg_buffer",
        "quotearg_alloc",
        "quotearg_alloc_mem",
        "quotearg_n_options",
        "quotearg_n",
        "quotearg",
        "quotearg_n_mem",
        "quotearg_mem",
        "quotearg_n_style",
        "quotearg_n_style_mem",
        "quotearg_style",
        "quotearg_style_mem",
        "quotearg_char",
        "quotearg_char_mem",
        "quotearg_colon",
        "quotearg_colon_mem",
        "quotearg_n_style_colon",
        "quotearg_n_custom",
        "quotearg_n_custom_mem",
        "quotearg_custom",
        "quotearg_custom_mem",
        "quote_n_mem",
        "quote_mem",
        "quote_n",
        "quote",
        "clone_quoting_options",
        "get_quoting_style",
        "set_quoting_style",
        "set_char_quoting",
        "set_quoting_flags",
        "set_custom_quoting",
        "quote_name",
        "quote_name_buf",
        "get_funky_string",
    }:
        return "quote_options"
    if base in {
        "xmalloc",
        "ximalloc",
        "xcharalloc",
        "xrealloc",
        "xirealloc",
        "xreallocarray",
        "xireallocarray",
        "xnmalloc",
        "xinmalloc",
        "x2realloc",
        "x2nrealloc",
        "xpalloc",
        "xzalloc",
        "xizalloc",
        "xcalloc",
        "xicalloc",
        "xmemdup",
        "ximemdup",
        "ximemdup0",
        "xstrdup",
        "xalloc_die",
    }:
        return "allocation"
    if base in {
        "rpl_mbrtowc",
        "mbrtowc",
        "unicode_to_mb",
        "mcel_scan",
        "mcel_scant",
        "is_utf8_charset",
    }:
        return "multibyte"
    if base in {"printf_parse", "print_formatted", "print_esc", "vasnprintf"}:
        return "printf_parser"
    if base in {
        "rpl_fopen",
        "rpl_fcntl",
        "freopen_safer",
        "stream_open",
        "close_stdin",
        "close_stdout",
        "rpl_fclose",
    }:
        return "libc_wrapper"
    if base in {"xstrtoimax", "xstrtoumax"}:
        return "numeric_parser"
    if base in {"strintcmp", "strnumcmp"}:
        return "numeric_compare"
    if base in {"find_field"}:
        return "field_selection"
    if base in {
        "cut_characters_mode",
        "cut_fields_mb_any",
        "cut_fields_bytesearch",
        "cut_file",
        "cut_bytes",
        "memchr2",
        "readtokens0",
        "set_fields",
        "add_range_pair",
        "oputs_",
    }:
        return "record_stream"
    if base in {
        "print_name_with_quoting",
        "print_long_format",
        "human_readable",
        "strftime_internal",
        "prompt",
        "version_etc_arn",
        "version_etc_ar",
        "version_etc_va",
        "version_etc",
        "emit_bug_reporting_address",
        "print_filename",
        "print_file_name_and_frills",
        "print_with_separator",
        "abformat_init",
        "calculate_columns",
        "print_current_files",
        "strmode",
    }:
        return "format_render"
    if base in {
        "gobble_file",
        "print_dir",
        "fdfile_has_aclinfo",
        "rm",
        "defaultcon",
        "restorecon_private",
        "restorecon",
        "re_protect",
        "renameatu",
        "streamsavedir",
        "excise",
        "find_in_given_path",
        "get_cgroup2_cpu_quota",
        "do_statx",
        "same_nameat",
        "set_process_security_ctx",
        "get_dir_status",
        "filesystem_type",
        "getuidbyname",
        "force_linkat",
        "force_symlinkat",
        "overwrite_ok",
        "extract_dirs_from_files",
    }:
        return "metadata_traversal"
    if base in {
        "write_line",
        "mergefps",
        "sortlines",
        "pipe_child",
        "merge",
        "mpsort_with_tmp",
        "sort_files",
        "init_node",
    }:
        return "sort_merge"
    if base in {
        "hash_print_statistics",
        "hash_insert_if_absent",
        "hash_rehash",
        "hash_remove",
    }:
        return "hash_table"
    if base in {"isaac_refill", "isaac_seed"}:
        return "hash_fold"
    if base in {"wc_lines_avx2", "wc_lines_avx512"}:
        return "vector_scan"
    if base in {"signal_setup"}:
        return "synchronization"
    if base in {"verrevcmp", "filenvercmp"}:
        return "version_compare"
    if base in {"mfile_name_concat", "areadlinkat_with_size"}:
        return "path_alloc"
    if base in {"try_tempname_len"}:
        return "tempname"
    if base in {"write_bytes"}:
        return "record_stream"
    if "copy" in base or base in {"sparse_copy", "copy_file_data", "do_copy"}:
        return "file_copy"
    if base.startswith("rpl_fts") or base.startswith("fts_"):
        return "fts"
    if base == "main":
        return "main"
    return base


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
    return len(RESIDUAL_MARKER_RE.findall(text))


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
    bare_register_matches = BARE_REGISTER_ARTIFACT_RE.findall(text)
    artifact_count = len(matches) + len(bare_register_matches)
    line_count = max(1, len(lines))
    return {
        "artifact_count": artifact_count,
        "raw_register_artifact_count": len(bare_register_matches),
        "per_line": round(artifact_count / line_count, 6),
    }


def _param_name_from_decl(decl: str) -> str | None:
    stripped = decl.strip()
    if not stripped or stripped == "void" or "..." in stripped:
        return None
    tokens = re.split(r"\s+", stripped.replace("*", " * "))
    for token in reversed(tokens):
        name = token.strip("*&[](),")
        if re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", name):
            return name
    return None


def shadowed_param_count(text: str) -> int:
    params: set[str] = set()
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith(("if ", "for ", "while ", "switch ")):
            continue
        match = HEADER_PARAM_RE.search(stripped)
        if not match:
            continue
        for part in match.group("params").split(","):
            name = _param_name_from_decl(part)
            if name:
                params.add(name)
        break
    if not params:
        return 0
    shadowed: set[str] = set()
    for line in text.splitlines():
        match = LOCAL_DECL_RE.search(line)
        if match and match.group("name") in params:
            shadowed.add(match.group("name"))
    return len(shadowed)


def declared_identifier_names(text: str, body_text: str) -> set[str]:
    names: set[str] = set()
    header = _first_function_header(text)
    for part in header.get("params") or []:
        name = _param_name_from_decl(str(part))
        if name:
            names.add(name)
    for line in body_text.splitlines():
        match = LOCAL_DECL_RE.search(line)
        if match:
            names.add(match.group("name"))
    return names


def undefined_identifier_return_count(text: str, body_text: str) -> int:
    declared = declared_identifier_names(text, body_text)
    builtin_return_names = {"NULL", "EOF", "true", "false", "EXIT_SUCCESS", "EXIT_FAILURE"}
    count = 0
    for match in RETURN_IDENTIFIER_RE.finditer(body_text):
        name = match.group("name")
        if name not in declared and name not in builtin_return_names:
            count += 1
    return count


def _source_body_text(text: str) -> str:
    start = text.find("{")
    return text[start + 1 :] if start >= 0 else text


def _strip_comments_and_whitespace(text: str) -> str:
    without_blocks = BLOCK_COMMENT_RE.sub("", text)
    without_lines = LINE_COMMENT_RE.sub("", without_blocks)
    return "".join(without_lines.split())


def comment_only_decompile(text: str) -> bool:
    return bool(text.strip()) and not _strip_comments_and_whitespace(text)


def _first_function_header(text: str) -> dict[str, Any]:
    for match in FUNCTION_HEADER_RE.finditer(text):
        name = match.group("name")
        if name in {"if", "for", "while", "switch", "return"}:
            continue
        raw_params = match.group("params").strip()
        if raw_params in ("", "void"):
            params: list[str] = []
        else:
            params = [part.strip() for part in raw_params.split(",") if part.strip()]
        return {
            "name": name,
            "ret_type": " ".join(match.group("ret").split()),
            "param_count": len(params),
            "params": params,
        }
    return {}


def _normalized_c_type(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    lowered = value.lower()
    lowered = re.sub(r"\b(?:const|volatile|restrict)\b", "", lowered)
    lowered = re.sub(r"\bstruct\s+", "struct ", lowered)
    lowered = re.sub(r"\s+", " ", lowered).strip()
    lowered = re.sub(r"\s*([*[\]])\s*", r"\1", lowered)
    return lowered


def is_void_type(value: Any) -> bool:
    return _normalized_c_type(value) == "void"


def has_return_statement(body_text: str) -> bool:
    return bool(re.search(r"\breturn\b", body_text))


def has_explicit_unresolved_summary_return(body_text: str) -> bool:
    return "summary return unresolved; value intentionally not reconstructed" in body_text


def _pointer_param_names(text: str) -> set[str]:
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith(("if ", "for ", "while ", "switch ")):
            continue
        match = HEADER_PARAM_RE.search(stripped)
        if not match:
            continue
        names: set[str] = set()
        for part in match.group("params").split(","):
            if "*" not in part and "[" not in part:
                continue
            name = _param_name_from_decl(part)
            if name:
                names.add(name)
        return names
    return set()


def pointer_scalar_compare_count(text: str, body_text: str) -> int:
    count = 0
    for name in sorted(_pointer_param_names(text)):
        escaped = re.escape(name)
        direct = re.compile(
            rf"\b{escaped}\s*(?:==|!=|<=|>=|<|>)\s*(?:0x[1-9a-f][0-9a-f]*|[1-9][0-9]*)\b",
            re.IGNORECASE,
        )
        reverse = re.compile(
            rf"\b(?:0x[1-9a-f][0-9a-f]*|[1-9][0-9]*)\s*(?:==|!=|<=|>=|<|>)\s*{escaped}\b",
            re.IGNORECASE,
        )
        count += len(direct.findall(body_text)) + len(reverse.findall(body_text))
    return count


def source_smell_metrics(text: str) -> dict[str, int]:
    body_text = _source_body_text(text)
    body_text_without_comments = LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", body_text))
    address_of_scalar_count = len(ADDRESS_OF_SCALAR_SMELL_RE.findall(body_text))
    local_stack_placeholder_count = len(LOCAL_STACK_PLACEHOLDER_RE.findall(body_text))
    stack_address_leak_count = len(STACK_ADDRESS_LEAK_RE.findall(body_text))
    shadow_count = shadowed_param_count(text)
    cast_expr_count = len(CAST_EXPR_RE.findall(body_text))
    pointer_cast_count = len(POINTER_CAST_RE.findall(body_text))
    control_flow_noise_count = len(CONTROL_FLOW_NOISE_RE.findall(body_text))
    orphan_break_count = (
        0
        if LOOP_OR_SWITCH_RE.search(body_text)
        else len(ORPHAN_BREAK_RE.findall(body_text))
    )
    call_readability_noise_count = len(CALL_READABILITY_NOISE_RE.findall(body_text))
    summary_pseudo_call_count = len(SUMMARY_PSEUDO_CALL_RE.findall(body_text))
    undefined_identifier_return_count_value = undefined_identifier_return_count(
        text, body_text_without_comments
    )
    unresolved_fcn_count = len(UNRESOLVED_FCN_RE.findall(body_text))
    argn_leak_count = len(ARGN_LEAK_RE.findall(body_text))
    raw_temp_stack_leak_count = len(RAW_TEMP_STACK_LEAK_RE.findall(body_text))
    fake_while_break_wrapper_count = len(FAKE_WHILE_BREAK_RE.findall(body_text))
    empty_loop_body_count = len(EMPTY_LOOP_BODY_RE.findall(body_text_without_comments))
    synthetic_type_leak_count = len(SYNTHETIC_TYPE_LEAK_RE.findall(body_text))
    pointer_scalar_compare_count_value = pointer_scalar_compare_count(text, body_text)
    readability_smell_count = (
        stack_address_leak_count
        + cast_expr_count
        + pointer_cast_count
        + control_flow_noise_count
        + orphan_break_count
        + call_readability_noise_count
        + summary_pseudo_call_count
        + undefined_identifier_return_count_value
        + argn_leak_count
        + raw_temp_stack_leak_count
        + fake_while_break_wrapper_count
        + empty_loop_body_count
        + synthetic_type_leak_count
        + pointer_scalar_compare_count_value
    )
    return {
        "address_of_scalar_count": address_of_scalar_count,
        "local_stack_placeholder_count": local_stack_placeholder_count,
        "stack_address_leak_count": stack_address_leak_count,
        "shadowed_param_count": shadow_count,
        "cast_expr_count": cast_expr_count,
        "pointer_cast_count": pointer_cast_count,
        "control_flow_noise_count": control_flow_noise_count,
        "orphan_break_count": orphan_break_count,
        "call_readability_noise_count": call_readability_noise_count,
        "summary_pseudo_call_count": summary_pseudo_call_count,
        "undefined_identifier_return_count": undefined_identifier_return_count_value,
        "unresolved_fcn_count": unresolved_fcn_count,
        "argn_leak_count": argn_leak_count,
        "raw_temp_stack_leak_count": raw_temp_stack_leak_count,
        "fake_while_break_wrapper_count": fake_while_break_wrapper_count,
        "empty_loop_body_count": empty_loop_body_count,
        "synthetic_type_leak_count": synthetic_type_leak_count,
        "pointer_scalar_compare_count": pointer_scalar_compare_count_value,
        "readability_smell_count": readability_smell_count,
        "source_smell_count": address_of_scalar_count
        + local_stack_placeholder_count
        + shadow_count,
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
    header = _first_function_header(text)
    body_text = _source_body_text(text)
    header_ret_type = header.get("ret_type") if header else None
    explicit_unresolved_summary_return = has_explicit_unresolved_summary_return(body_text)
    missing_return_nonvoid = (
        bool(header_ret_type)
        and not is_void_type(header_ret_type)
        and not has_return_statement(body_text)
        and not explicit_unresolved_summary_return
    )
    metrics.update(
        {
            "classification": classification,
            "fallback_marker": fallback,
            "residual_markers": residuals,
            "empty": empty,
            "comment_only": comment_only_decompile(text),
            "header_ret_type": header_ret_type,
            "header_ret_type_normalized": _normalized_c_type(header_ret_type),
            "header_param_count": header.get("param_count") if header else None,
            "header_name": header.get("name") if header else None,
            "has_return_statement": has_return_statement(body_text),
            "explicit_unresolved_summary_return": explicit_unresolved_summary_return,
            "missing_return_nonvoid": missing_return_nonvoid,
            **source_smell_metrics(text),
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


def plugin_search_path(path: str) -> str:
    candidate = Path(path).expanduser()
    if not candidate.is_absolute():
        candidate = (Path.cwd() / candidate).resolve()
    return str(candidate)


def staged_plugin_dir(plugin_paths: list[str], tmpdir: Path | None) -> str:
    if not plugin_paths:
        return ""
    if len(plugin_paths) == 1 or tmpdir is None:
        return plugin_paths[0]
    root = tmpdir / "plugins"
    root.mkdir(parents=True, exist_ok=True)
    for raw_path in plugin_paths:
        source = Path(raw_path)
        if not source.is_dir():
            continue
        for child in source.iterdir():
            target = root / child.name
            if target.exists() or target.is_symlink():
                continue
            try:
                os.symlink(child, target, target_is_directory=child.is_dir())
            except OSError:
                continue
    return str(root)


def build_r2_env(
    r2: str,
    plugin_dir: str,
    baseline_plugin_dirs: list[str] | tuple[str, ...],
    tmpdir: Path | None,
) -> dict[str, str]:
    env = os.environ.copy()
    plugin_paths = [plugin_search_path(plugin_dir)] if plugin_dir else []
    plugin_paths.extend(plugin_search_path(path) for path in baseline_plugin_dirs if path)
    if tmpdir is not None:
        tmpdir.mkdir(parents=True, exist_ok=True)
    plugin_path = staged_plugin_dir(plugin_paths, tmpdir)
    if plugin_path:
        env["R2_USER_PLUGINS"] = plugin_path
        env["R2_LIBR_PLUGINS"] = plugin_path
    if tmpdir is not None:
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


SAFE_COMPONENT_RE = re.compile(r"[^A-Za-z0-9_.-]+")


def safe_path_component(value: Any) -> str:
    cleaned = SAFE_COMPONENT_RE.sub("_", str(value).strip())
    cleaned = cleaned.strip("._-")
    return cleaned[:48] or "task"


def task_env(
    base_env: dict[str, str] | None,
    tmpdir: Path | None,
    *components: Any,
) -> dict[str, str] | None:
    if tmpdir is None:
        return base_env
    env = dict(base_env or os.environ.copy())
    raw_slug = "__".join(safe_path_component(component) for component in components)
    if len(raw_slug) > 180:
        digest = hashlib.sha256(raw_slug.encode("utf-8")).hexdigest()[:16]
        raw_slug = f"{raw_slug[:150]}__{digest}"
    root = tmpdir / "workers" / raw_slug
    home = root / "home"
    xdg_data = root / "xdg-data"
    root.mkdir(parents=True, exist_ok=True)
    home.mkdir(parents=True, exist_ok=True)
    xdg_data.mkdir(parents=True, exist_ok=True)
    env["HOME"] = str(home)
    env["TMPDIR"] = str(root)
    env["TMP"] = str(root)
    env["TEMP"] = str(root)
    env["XDG_DATA_HOME"] = str(xdg_data)
    return env


def parallel_split(total_jobs: int, case_count: int) -> tuple[int, int]:
    jobs = max(1, total_jobs)
    if jobs == 1 or case_count <= 1:
        return 1, jobs
    case_jobs = min(case_count, max(1, int(jobs**0.5)))
    command_jobs = max(1, jobs // case_jobs)
    return case_jobs, command_jobs


def run_ordered_parallel(
    items: list[T],
    jobs: int,
    worker: Callable[[T], U],
) -> list[U]:
    if jobs <= 1 or len(items) <= 1:
        return [worker(item) for item in items]
    results: list[U | None] = [None] * len(items)
    max_workers = min(max(1, jobs), len(items))
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(worker, item): idx for idx, item in enumerate(items)}
        for future in concurrent.futures.as_completed(futures):
            results[futures[future]] = future.result()
    return cast(list[U], results)


def prepend_path(prefix: str, existing: str) -> str:
    if not existing:
        return prefix
    return f"{prefix}:{existing}"


def subprocess_text(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return ""


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
        stdout = subprocess_text(exc.stdout)
        stderr = subprocess_text(exc.stderr)
        return CmdResult(
            returncode=124,
            stdout=stdout,
            stderr=stderr or f"timeout after {timeout_s}s",
            elapsed_s=time.perf_counter() - start,
        )


def read_manifest(
    path: Path,
    default_analysis: str,
    default_max_functions: int,
    override_max_functions: bool = False,
) -> list[BinaryCase]:
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
        max_functions = (
            default_max_functions
            if override_max_functions
            else int(item.get("max_functions", default_max_functions))
        )
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


def focused_coreutils_cases(
    root_value: str,
    default_analysis: str,
    default_max_functions: int,
) -> list[BinaryCase]:
    if not root_value:
        return []
    root = Path(root_value)
    cases: list[BinaryCase] = []
    for name, target in COREUTILS_FOCUSED_TARGETS:
        path = root / name
        if not is_executable(path):
            continue
        cases.append(
            BinaryCase(
                name=name,
                path=path,
                corpus="coreutils",
                analysis=default_analysis,
                targets=(target,),
                max_functions=default_max_functions,
            )
        )
    return cases


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
        cases.extend(
            read_manifest(
                Path(args.manifest),
                args.analysis,
                args.max_functions,
                bool(getattr(args, "override_manifest_max_functions", False)),
            )
        )
    if args.binary:
        cases.extend(direct_binary_cases(args.binary, args.target, args.analysis, args.max_functions))
    if args.manifest_only:
        return dedupe_cases(cases)
    if not args.no_repo_fixtures:
        cases.extend(repo_fixture_cases(args.analysis, args.max_functions))
    if args.focused_coreutils:
        cases.extend(focused_coreutils_cases(args.coreutils_dir, args.analysis, args.max_functions))
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
    command = f"{case.analysis}; aflj"
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
        candidates.sort(key=lambda f: target_candidate_rank(target, f))
        if not candidates:
            selected.append({"requested": target, "found": False, "target_match": "missing"})
            continue
        fcn = candidates[0]
        if fcn["addr"] in seen_addrs:
            continue
        seen_addrs.add(fcn["addr"])
        selected.append(annotate_target_match(target, fcn))
    if selected:
        return selected

    sample_pool = [fcn for fcn in functions if is_sampleable_function(fcn)]
    if not sample_pool:
        return selected
    top = sorted(sample_pool, key=lambda f: (-int(f.get("size") or 0), -int(f.get("blocks") or 0), f["addr"], f["name"]))
    for fcn in top[: max(0, limit)]:
        selected.append({**fcn, "requested": fcn["name"], "found": True, "target_match": "sampled"})
    selected.sort(key=lambda f: (not f.get("found", False), f.get("addr", 0), f.get("name", "")))
    return selected


def is_sampleable_function(fcn: dict[str, Any]) -> bool:
    """Return whether automatic corpus sampling should treat FCN as real code."""
    name = str(fcn.get("name") or "")
    norm = normalize_symbol(name)
    try:
        addr = int(fcn.get("addr") or 0)
    except (TypeError, ValueError):
        addr = 0
    if addr <= 0:
        return False
    lowered = name.lower()
    if lowered.startswith("sym.imp."):
        return False
    if UNSAMPLED_CODE_NAME_RE.match(norm):
        return False
    if norm in {
        "fini",
        "init",
        "start",
        "do_global_dtors_aux",
        "call_weak_fn",
        "deregister_tm_clones",
        "entry.fini0",
        "entry.init0",
        "entry0",
        "frame_dummy",
        "register_tm_clones",
    }:
        return False
    return True


def cache_counter_metrics(payload: Any) -> dict[str, int] | None:
    if not isinstance(payload, dict):
        return None
    out: dict[str, int] = {}
    for field in CACHE_COUNTER_FIELDS:
        value = payload.get(field)
        if isinstance(value, int) and not isinstance(value, bool):
            out[field] = value
    return out or None


def engine_cache_metrics(payload: Any) -> dict[str, dict[str, int]] | None:
    if not isinstance(payload, dict):
        return None
    out: dict[str, dict[str, int]] = {}
    for partition in ("analysis", "artifacts", "renders", "total"):
        counters = cache_counter_metrics(payload.get(partition))
        if counters:
            out[partition] = counters
    return out or None


def payload_cache_metrics(payload: Any) -> dict[str, Any] | None:
    if not isinstance(payload, dict):
        return None
    out: dict[str, Any] = {}
    engine_cache = engine_cache_metrics(payload.get("engine_cache"))
    if engine_cache:
        out["engine_cache"] = engine_cache
    for key in CACHE_METRIC_KEYS:
        counters = cache_counter_metrics(payload.get(key))
        if counters:
            out[key] = counters
    return out or None


def cache_metrics_have_hits(metrics: Any) -> bool:
    if isinstance(metrics, dict):
        hit_value = metrics.get("hits")
        if isinstance(hit_value, int) and not isinstance(hit_value, bool) and hit_value > 0:
            return True
        return any(cache_metrics_have_hits(value) for value in metrics.values())
    return False


def phase_timing_metrics(payload: Any) -> dict[str, int] | None:
    if not isinstance(payload, list):
        return None
    out: dict[str, int] = {}
    for item in payload:
        if not isinstance(item, dict):
            continue
        phase = item.get("phase")
        elapsed = item.get("elapsed_us")
        if isinstance(phase, str) and isinstance(elapsed, int) and not isinstance(elapsed, bool):
            out[phase] = out.get(phase, 0) + elapsed
    return dict(sorted(out.items())) or None


def plan_variant(value: Any) -> str | None:
    if isinstance(value, str):
        return value
    if isinstance(value, dict) and len(value) == 1:
        key = next(iter(value))
        return str(key)
    return None


def command_fast_path_metrics(payload: Any, cache_metrics: dict[str, Any] | None = None) -> dict[str, Any] | None:
    if not isinstance(payload, dict):
        return None
    out: dict[str, Any] = {}
    for field in FAST_PATH_BOOL_FIELDS:
        value = payload.get(field)
        if isinstance(value, bool):
            out[field] = value
    for field in FAST_PATH_COUNTER_FIELDS:
        value = payload.get(field)
        if isinstance(value, int) and not isinstance(value, bool):
            out[field] = value

    timings = phase_timing_metrics(payload.get("phase_timings"))
    if timings:
        out["phase_timings_us"] = timings
        for phase in ("interproc_summary", "semantic_summary", "semantic_artifact"):
            if phase in timings:
                out[f"{phase}_us"] = timings[phase]

    interproc = payload.get("interproc")
    if isinstance(interproc, dict):
        for source_key, dest_key in (
            ("callsite_count", "interproc_callsite_count"),
            ("iterations", "interproc_iterations"),
            ("max_iterations", "interproc_max_iterations"),
        ):
            value = interproc.get(source_key)
            if isinstance(value, int) and not isinstance(value, bool):
                out[dest_key] = value
        if isinstance(interproc.get("converged"), bool):
            out["interproc_converged"] = interproc["converged"]
        if "summary" in interproc:
            out["interproc_has_summary"] = interproc.get("summary") is not None

    compiled = payload.get("compiled_semantics")
    if not isinstance(compiled, dict):
        compiled = payload.get("semantic")
    if isinstance(compiled, dict):
        for source_key, dest_key in (
            ("granularity", "semantic_granularity"),
            ("execution", "semantic_execution"),
            ("slice_class", "slice_class"),
        ):
            value = compiled.get(source_key)
            if isinstance(value, str):
                out[dest_key] = value
        for field in SEMANTIC_SUMMARY_COUNT_FIELDS:
            value = compiled.get(field)
            if isinstance(value, int) and not isinstance(value, bool):
                out[field] = value
        if compiled.get("granularity") == "summary_only":
            out["summary_only"] = True

    plans = payload.get("plans")
    if isinstance(plans, dict):
        for source_key, dest_key in (
            ("artifact_build", "artifact_build_plan"),
            ("query", "query_plan"),
            ("type_plan", "type_plan"),
            ("decompile", "decompile_plan"),
        ):
            variant = plan_variant(plans.get(source_key))
            if variant:
                out[dest_key] = variant
    for source_key, dest_key in (
        ("query_plan", "query_plan"),
        ("type_plan", "type_plan"),
        ("decompile_plan", "decompile_plan"),
    ):
        variant = plan_variant(compiled.get(source_key)) if isinstance(compiled, dict) else None
        if variant and dest_key not in out:
            out[dest_key] = variant

    prefer_bounded = payload.get("prefer_bounded_type_plan")
    if isinstance(prefer_bounded, bool):
        out["prefer_bounded_type_plan"] = prefer_bounded
    if cache_metrics is not None:
        out["cache_hit"] = cache_metrics_have_hits(cache_metrics)
    if "summary_fast_path" not in out:
        summary_fast_path = bool(
            out.get("summary_only")
            or out.get("type_plan") == "VmSummaryOnly"
            or out.get("decompile_plan") in {"NativeSummaryIslands", "VmSummaryOnly"}
            or int(out.get("native_region_summary_count") or 0) > 0
            or int(out.get("native_worker_summary_count") or 0) > 0
        )
        if summary_fast_path or out:
            out["summary_fast_path"] = summary_fast_path
    return out or None


def command_summary(
    name: str,
    result: CmdResult,
    include_sensitive: bool,
    *,
    case: BinaryCase | None = None,
    target: dict[str, Any] | None = None,
    gold_manifest: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    entry: dict[str, Any] = {
        "returncode": result.returncode,
        "timeout": result.returncode == 124,
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
            if isinstance(payload, dict):
                cache_metrics = payload_cache_metrics(payload)
                if cache_metrics:
                    entry["cache_metrics"] = cache_metrics
                fast_path_metrics = command_fast_path_metrics(payload, cache_metrics)
                if fast_path_metrics:
                    entry["fast_path_metrics"] = fast_path_metrics
            if name == "profile" and isinstance(payload, dict):
                cache_metrics = entry.get("cache_metrics") if isinstance(entry.get("cache_metrics"), dict) else {}
                decompile_cache = (
                    cache_metrics.get("decompile_cache")
                    if isinstance(cache_metrics.get("decompile_cache"), dict)
                    else None
                )
                engine_cache = (
                    cache_metrics.get("engine_cache")
                    if isinstance(cache_metrics.get("engine_cache"), dict)
                    else None
                )
                profile_metrics = {
                    "count": payload.get("count") if isinstance(payload.get("count"), int) else None,
                    "cache_hits": decompile_cache.get("hits") if decompile_cache else None,
                    "cache_misses": decompile_cache.get("misses") if decompile_cache else None,
                }
                if decompile_cache:
                    profile_metrics["decompile_cache"] = decompile_cache
                if engine_cache:
                    profile_metrics["engine_cache"] = engine_cache
                entry["profile_metrics"] = {
                    key: value
                    for key, value in profile_metrics.items()
                    if value is not None
                }
        except ValueError as exc:
            entry["json_error"] = str(exc)
    if name.startswith(DECOMPILE_COMMAND_PREFIX):
        quality = decompile_quality(result.stdout)
        entry["decompile_quality"] = quality
        if quality["fallback_marker"] is not None:
            entry["fallback_marker"] = quality["fallback_marker"]
        entry["residual_markers"] = quality["residual_markers"]
        entry["empty"] = quality["empty"]
    attach_gold_oracle(
        entry,
        case=case,
        target=target,
        command=name,
        stdout=result.stdout,
        gold_manifest=gold_manifest,
    )
    return entry


def command_event(
    *,
    case: BinaryCase,
    target: dict[str, Any],
    command: str,
    repeat_idx: int,
    started_at: float,
    ended_at: float,
    timeout_s: int,
    returncode: int | None,
) -> dict[str, Any]:
    return {
        "case": case.name,
        "corpus": case.corpus,
        "target": target.get("name") or target.get("requested"),
        "addr": target.get("addr"),
        "command": command,
        "repeat_idx": repeat_idx,
        "started_at": round(started_at, 6),
        "ended_at": round(ended_at, 6),
        "elapsed_s": round(max(0.0, ended_at - started_at), 6),
        "timeout_s": timeout_s,
        "timeout": returncode == 124,
        "returncode": returncode,
    }


def parse_command_filter(value: str) -> tuple[str, ...]:
    if not value.strip():
        return DEFAULT_TARGET_COMMANDS
    names: list[str] = []
    for raw in value.split(","):
        name = raw.strip()
        if not name:
            continue
        if name not in TARGET_COMMAND_DEFS:
            choices = ", ".join(TARGET_COMMAND_DEFS)
            raise ValueError(f"unknown benchmark command {name!r}; choices: {choices}")
        if name not in names:
            names.append(name)
    if not names:
        raise ValueError("at least one benchmark command must be selected")
    return tuple(names)


def _symbol_match_keys(value: Any) -> set[str]:
    if not isinstance(value, str) or not value.strip():
        return set()
    text = value.strip()
    keys = {text}
    normalized = normalize_symbol(text)
    if normalized:
        keys.add(normalized)
        keys.add(f"sym.{normalized}")
        keys.add(f"dbg.{normalized}")
    return keys


def load_gold_manifest(path: Path | str | None) -> list[dict[str, Any]]:
    if path is None or not str(path).strip():
        return []
    manifest_path = Path(path)
    payload = json.loads(manifest_path.read_text())
    if not isinstance(payload, dict):
        raise ValueError("gold manifest must be a JSON object")
    raw_expectations = payload.get("expectations", payload.get("targets", []))
    if not isinstance(raw_expectations, list):
        raise ValueError("gold manifest expects a top-level expectations array")
    expectations: list[dict[str, Any]] = []
    for idx, raw in enumerate(raw_expectations):
        if not isinstance(raw, dict):
            raise ValueError(f"gold expectation {idx} must be an object")
        target = raw.get("target")
        if not isinstance(target, str) or not target.strip():
            raise ValueError(f"gold expectation {idx} needs a target")
        command = raw.get("command", "decompile_sla")
        if not isinstance(command, str) or not command.strip():
            raise ValueError(f"gold expectation {idx} needs a command")
        expectation = dict(raw)
        expectation["target"] = target.strip()
        expectation["command"] = command.strip()
        expectation.setdefault("id", f"gold-{idx}")
        expectations.append(expectation)
    expectations.sort(
        key=lambda item: (
            str(item.get("corpus") or ""),
            str(item.get("case") or item.get("binary") or ""),
            str(item.get("target") or ""),
            str(item.get("command") or ""),
            str(item.get("id") or ""),
        )
    )
    return expectations


def gold_manifest_hash(path: str) -> str | None:
    if not path.strip():
        return None
    return file_sha256(Path(path))


def _gold_field_matches(expected: Any, actual_values: set[str]) -> bool:
    if expected is None:
        return True
    if isinstance(expected, str):
        return bool(_symbol_match_keys(expected) & actual_values)
    if isinstance(expected, list):
        return any(_gold_field_matches(item, actual_values) for item in expected)
    return False


def gold_expectations_for_command(
    gold_manifest: list[dict[str, Any]] | None,
    case: BinaryCase | None,
    target: dict[str, Any] | None,
    command: str,
) -> list[dict[str, Any]]:
    if not gold_manifest or case is None or target is None:
        return []
    target_keys: set[str] = set()
    for value in (target.get("name"), target.get("requested"), target.get("target_alias")):
        if isinstance(value, dict):
            target_keys.update(_symbol_match_keys(value.get("requested")))
            target_keys.update(_symbol_match_keys(value.get("matched")))
        else:
            target_keys.update(_symbol_match_keys(value))
    case_keys = _symbol_match_keys(case.name)
    case_keys.update(_symbol_match_keys(case.path.name))
    corpus_keys = {case.corpus}

    matched: list[dict[str, Any]] = []
    for expectation in gold_manifest:
        if str(expectation.get("command", "decompile_sla")) != command:
            continue
        if not _gold_field_matches(expectation.get("target"), target_keys):
            continue
        if not _gold_field_matches(expectation.get("case", expectation.get("binary")), case_keys):
            continue
        if not _gold_field_matches(expectation.get("corpus"), corpus_keys):
            continue
        matched.append(expectation)
    return matched


def gold_oracle_failures_for_output(
    *,
    case: BinaryCase,
    target_name: str,
    command: str,
    stdout: str,
    expectations: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    for expectation in expectations:
        expectation_id = str(expectation.get("id") or "")
        owner = str(expectation.get("owner") or "unknown")
        for check, patterns in (
            ("contains", expectation.get("contains", [])),
            ("regex", expectation.get("regex", [])),
            ("not_contains", expectation.get("not_contains", [])),
            ("not_regex", expectation.get("not_regex", [])),
        ):
            if isinstance(patterns, str):
                pattern_list = [patterns]
            elif isinstance(patterns, list):
                pattern_list = [str(pattern) for pattern in patterns]
            else:
                pattern_list = []
            for pattern in pattern_list:
                matched = (
                    re.search(pattern, stdout, re.MULTILINE) is not None
                    if check.endswith("regex")
                    else pattern in stdout
                )
                failed = matched if check.startswith("not_") else not matched
                if failed:
                    failures.append(
                        {
                            "kind": GOLD_ORACLE_FAILURE,
                            "case": case.name,
                            "corpus": case.corpus,
                            "target": target_name,
                            "command": command,
                            "expectation": expectation_id,
                            "check": check,
                            "pattern": pattern,
                            "owner": owner,
                        }
                    )
    failures.sort(
        key=lambda item: (
            str(item.get("expectation") or ""),
            str(item.get("check") or ""),
            str(item.get("pattern") or ""),
        )
    )
    return failures


def attach_gold_oracle(
    entry: dict[str, Any],
    *,
    case: BinaryCase | None,
    target: dict[str, Any] | None,
    command: str,
    stdout: str,
    gold_manifest: list[dict[str, Any]] | None,
) -> None:
    expectations = gold_expectations_for_command(gold_manifest, case, target, command)
    if not expectations or case is None or target is None:
        return
    target_name = str(target.get("name") or target.get("requested") or "")
    failures = gold_oracle_failures_for_output(
        case=case,
        target_name=target_name,
        command=command,
        stdout=stdout,
        expectations=expectations,
    )
    entry["gold_oracle"] = {
        "status": "ok" if not failures else "failed",
        "expectation_count": len(expectations),
        "failures": failures,
    }


def target_commands(command_names: tuple[str, ...] | None = None) -> dict[str, str]:
    names = command_names or DEFAULT_TARGET_COMMANDS
    return {name: TARGET_COMMAND_DEFS[name] for name in names}


def batched_section_start(name: str, repeat_idx: int) -> str:
    return f"{BATCH_SENTINEL} START {name} {repeat_idx}"


def batched_section_end(name: str, repeat_idx: int) -> str:
    return f"{BATCH_SENTINEL} END {name} {repeat_idx}"


def batched_time_marker(kind: str, name: str, repeat_idx: int) -> str:
    return f"{BATCH_SENTINEL} TIME_{kind} {name} {repeat_idx}"


def parse_batched_output_detailed(
    stdout: str,
) -> tuple[
    dict[tuple[str, int], str],
    dict[tuple[str, int], tuple[int | None, int | None]],
    set[tuple[str, int]],
    set[tuple[str, int]],
]:
    sections: dict[tuple[str, int], list[str]] = {}
    timings: dict[tuple[str, int], list[int | None]] = {}
    started_sections: set[tuple[str, int]] = set()
    completed_sections: set[tuple[str, int]] = set()
    pending_time: tuple[str, tuple[str, int]] | None = None
    active: tuple[str, int] | None = None
    active_lines: list[str] = []
    for line in stdout.splitlines():
        if pending_time is not None:
            kind, key = pending_time
            if line.strip().isdigit():
                timing = timings.setdefault(key, [None, None])
                timing[0 if kind == "START" else 1] = int(line.strip())
                pending_time = None
                continue
            pending_time = None
        if line.startswith(f"{BATCH_SENTINEL} "):
            parts = line.split()
            if len(parts) == 4 and parts[1] in ("START", "END"):
                key = (parts[2], int(parts[3])) if parts[3].isdigit() else None
                if parts[1] == "START" and key is not None:
                    if active is not None:
                        sections[active] = active_lines
                    active = key
                    started_sections.add(key)
                    active_lines = []
                    continue
                if parts[1] == "END" and key is not None and active == key:
                    sections[active] = active_lines
                    completed_sections.add(key)
                    active = None
                    active_lines = []
                    continue
            if len(parts) == 4 and parts[1] in ("TIME_START", "TIME_END"):
                key = (parts[2], int(parts[3])) if parts[3].isdigit() else None
                if key is not None:
                    pending_time = ("START" if parts[1] == "TIME_START" else "END", key)
                    continue
        if active is not None:
            active_lines.append(line)
    if active is not None:
        sections[active] = active_lines
    section_payloads = {
        key: "\n".join(lines).rstrip("\n") + ("\n" if lines else "")
        for key, lines in sections.items()
    }
    return section_payloads, {
        key: (value[0], value[1]) for key, value in timings.items()
    }, started_sections, completed_sections


def parse_batched_output(
    stdout: str,
) -> tuple[dict[tuple[str, int], str], dict[tuple[str, int], tuple[int | None, int | None]]]:
    sections, timings, _started, _completed = parse_batched_output_detailed(stdout)
    return sections, timings


def parse_batched_sections(stdout: str) -> dict[tuple[str, int], str]:
    sections, _timings = parse_batched_output(stdout)
    return sections


def batched_target_script(
    case: BinaryCase,
    addr: int,
    repeat: int,
    commands: dict[str, str],
) -> list[tuple[str, int, str, str]]:
    sections: list[tuple[str, int, str, str]] = []
    for name, command in commands.items():
        per_command_repeats = max(1, repeat) if name in DECOMPILE_REPEAT_COMMANDS else 1
        for repeat_idx in range(per_command_repeats):
            sections.append((name, repeat_idx, batched_section_start(name, repeat_idx), command))
    return sections


def target_section_name(target_idx: int, command: str) -> str:
    return f"t{target_idx}_{command}"


def target_setup_name(target_idx: int) -> str:
    return f"t{target_idx}_setup"


def target_batches(
    targets: list[dict[str, Any]],
    batch_target_size: int,
) -> list[list[dict[str, Any]]]:
    if batch_target_size <= 0 or len(targets) <= batch_target_size:
        return [targets]
    return [
        targets[idx : idx + batch_target_size]
        for idx in range(0, len(targets), batch_target_size)
    ]


def batched_section_returncode(batch_returncode: int, section_completed: bool) -> int:
    if section_completed:
        return 0
    return 124 if batch_returncode == 124 else batch_returncode


def batched_section_status(
    *,
    key: tuple[str, int],
    timings: dict[tuple[str, int], tuple[int | None, int | None]],
    started_sections: set[tuple[str, int]],
    completed_sections: set[tuple[str, int]],
    batch_returncode: int,
    blocked_by_setup: bool = False,
) -> str:
    if key in completed_sections:
        return BATCH_SECTION_COMPLETED
    start_ns, end_ns = timings.get(key, (None, None))
    if key in started_sections or start_ns is not None:
        if batch_returncode == 124 and end_ns is None:
            return BATCH_SECTION_STARTED_TIMEOUT
        return BATCH_SECTION_STARTED_FAILED
    if blocked_by_setup:
        return BATCH_SECTION_SETUP_FAILED
    return BATCH_SECTION_NOT_REACHED


def setup_section_status(
    *,
    start_ns: int | None,
    end_ns: int | None,
    batch_returncode: int,
    blocked_by_setup: bool = False,
) -> str:
    if blocked_by_setup:
        return BATCH_SECTION_SETUP_FAILED
    if start_ns is not None and end_ns is not None:
        return BATCH_SECTION_COMPLETED
    if start_ns is not None and batch_returncode == 124:
        return BATCH_SECTION_STARTED_TIMEOUT
    return BATCH_SECTION_NOT_REACHED


def returncode_for_section_status(batch_returncode: int, status: str) -> int | None:
    if status == BATCH_SECTION_COMPLETED:
        return 0
    if status == BATCH_SECTION_STARTED_TIMEOUT:
        return 124
    if status == BATCH_SECTION_STARTED_FAILED:
        return batch_returncode
    return None


def section_status_incomplete(status: Any) -> bool:
    return status in INCOMPLETE_SECTION_STATUSES


def skipped_command_summary(
    name: str,
    status: str,
    event: dict[str, Any],
    include_sensitive: bool,
) -> dict[str, Any]:
    return {
        "returncode": None,
        "timeout": False,
        "elapsed_s": 0.0,
        "runtime_bucket": "skipped",
        "stdout": summarize_text("", include_preview=include_sensitive),
        "execution_mode": "batched",
        "section_status": status,
        "skipped": True,
        "event": event,
    }


def command_entry_timed_out(entry: dict[str, Any]) -> bool:
    event = entry.get("event")
    if bool(entry.get("timeout")) or bool(
        isinstance(event, dict) and event.get("timeout")
    ):
        return True
    repeat = entry.get("repeat")
    repeat_events = repeat.get("events") if isinstance(repeat, dict) else None
    return isinstance(repeat_events, list) and any(
        isinstance(repeat_event, dict) and repeat_event.get("timeout")
        for repeat_event in repeat_events
    )


def target_has_timed_out_command(target: dict[str, Any]) -> bool:
    if not target.get("found", True):
        return False
    for entry in target.get("commands", {}).values():
        if isinstance(entry, dict) and command_entry_timed_out(entry):
            return True
    return False


def command_entry_needs_retry(entry: dict[str, Any]) -> bool:
    if command_entry_timed_out(entry):
        return True
    section_status = entry.get("section_status")
    if section_status in {BATCH_SECTION_STARTED_FAILED, BATCH_SECTION_STARTED_TIMEOUT}:
        return True
    returncode = entry.get("returncode")
    return returncode not in (None, 0)


def target_batch_failed(target: dict[str, Any]) -> bool:
    batch_event = target.get("batch_event")
    if not isinstance(batch_event, dict):
        return False
    return batch_event.get("returncode") not in (None, 0, 124)


def target_has_retryable_command(target: dict[str, Any]) -> bool:
    if not target.get("found", True):
        return False
    batch_failed = target_batch_failed(target)
    for entry in target.get("commands", {}).values():
        if isinstance(entry, dict) and command_entry_needs_retry(entry):
            return True
        if (
            batch_failed
            and isinstance(entry, dict)
            and section_status_incomplete(entry.get("section_status"))
        ):
            return True
    return False


def timed_out_command_names(target: dict[str, Any]) -> set[str]:
    if not target.get("found", True):
        return set()
    return {
        name
        for name, entry in target.get("commands", {}).items()
        if isinstance(name, str)
        and isinstance(entry, dict)
        and command_entry_timed_out(entry)
    }


def retryable_command_names(target: dict[str, Any]) -> set[str]:
    if not target.get("found", True):
        return set()
    batch_failed = target_batch_failed(target)
    return {
        name
        for name, entry in target.get("commands", {}).items()
        if isinstance(name, str)
        and isinstance(entry, dict)
        and (
            command_entry_needs_retry(entry)
            or (batch_failed and section_status_incomplete(entry.get("section_status")))
        )
    }


def annotate_attribution(
    target: dict[str, Any],
    mode: str,
    *,
    retry_origin: str | None = None,
) -> dict[str, Any]:
    target["attribution_mode"] = mode
    if retry_origin:
        target["retry_origin"] = retry_origin
    for event_key in ("batch_event", "setup_event"):
        event = target.get(event_key)
        if isinstance(event, dict):
            event["attribution_mode"] = mode
            if retry_origin:
                event["retry_origin"] = retry_origin
    for event in target.get("command_events", []):
        if isinstance(event, dict):
            event["attribution_mode"] = mode
            if retry_origin:
                event["retry_origin"] = retry_origin
    for entry in target.get("commands", {}).values():
        if isinstance(entry, dict):
            entry["attribution_mode"] = mode
            if retry_origin:
                entry["retry_origin"] = retry_origin
            event = entry.get("event")
            if isinstance(event, dict):
                event["attribution_mode"] = mode
                if retry_origin:
                    event["retry_origin"] = retry_origin
            repeat = entry.get("repeat")
            events = repeat.get("events") if isinstance(repeat, dict) else None
            if isinstance(events, list):
                for repeat_event in events:
                    if isinstance(repeat_event, dict):
                        repeat_event["attribution_mode"] = mode
                        if retry_origin:
                            repeat_event["retry_origin"] = retry_origin
    return target


def timed_event_from_ns(
    *,
    case: BinaryCase,
    target: dict[str, Any],
    command: str,
    repeat_idx: int,
    start_ns: int | None,
    end_ns: int | None,
    fallback_started_at: float,
    fallback_elapsed: float,
    timeout_s: int,
    returncode: int | None,
    batch_elapsed: float,
    section_status: str | None = None,
) -> dict[str, Any]:
    elapsed = (
        max(0.0, (end_ns - start_ns) / 1_000_000_000.0)
        if start_ns is not None and end_ns is not None and end_ns >= start_ns
        else fallback_elapsed
    )
    started_at = start_ns / 1_000_000_000.0 if start_ns is not None else fallback_started_at
    ended_at = end_ns / 1_000_000_000.0 if end_ns is not None else started_at + elapsed
    event = command_event(
        case=case,
        target=target,
        command=command,
        repeat_idx=repeat_idx,
        started_at=started_at,
        ended_at=ended_at,
        timeout_s=timeout_s,
        returncode=returncode,
    )
    event["batch_elapsed_s"] = round(batch_elapsed, 6)
    event["timed"] = start_ns is not None and end_ns is not None
    if section_status is not None:
        event["section_status"] = section_status
    return event


def collect_target_batched(
    r2: str,
    case: BinaryCase,
    target: dict[str, Any],
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    task_tmpdir: Path | None,
    runner: Runner,
    commands: dict[str, str] | None = None,
    gold_manifest: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    if not target.get("found", True):
        return dict(target)
    commands = commands or target_commands()
    addr = int(target["addr"])
    prefix = f"{case.analysis}; s 0x{addr:x}; af"
    sections = batched_target_script(case, addr, repeat, commands)
    command_parts = [
        f"?e {batched_time_marker('START', 'setup', 0)}",
        "!date +%s%N",
        prefix,
        f"?e {batched_time_marker('END', 'setup', 0)}",
        "!date +%s%N",
    ]
    for name, repeat_idx, start, command in sections:
        command_parts.append(f"?e {batched_time_marker('START', name, repeat_idx)}")
        command_parts.append("!date +%s%N")
        command_parts.append(f"?e {start}")
        command_parts.append(command)
        command_parts.append(f"?e {batched_section_end(name, repeat_idx)}")
        command_parts.append(f"?e {batched_time_marker('END', name, repeat_idx)}")
        command_parts.append("!date +%s%N")
    command_env = task_env(env, task_tmpdir, case.corpus, case.name, f"target-0x{addr:x}", "batched")
    started_at = time.time()
    result = runner(r2, case.path, "; ".join(command_parts), timeout_s, command_env)
    ended_at = time.time()
    parsed, timings, started_sections, completed_sections = parse_batched_output_detailed(
        result.stdout
    )
    out: dict[str, Any] = dict(target)
    out["execution_mode"] = "batched"
    out["commands"] = {}
    out["command_events"] = []
    batch_elapsed = max(0.0, ended_at - started_at)
    batch_event = {
        "case": case.name,
        "corpus": case.corpus,
        "target": target.get("name") or target.get("requested"),
        "addr": target.get("addr"),
        "command": "batch",
        "repeat_idx": 0,
        "started_at": round(started_at, 6),
        "ended_at": round(ended_at, 6),
        "elapsed_s": round(batch_elapsed, 6),
        "timeout_s": timeout_s,
        "timeout": result.returncode == 124,
        "returncode": result.returncode,
    }
    out["batch_event"] = batch_event
    setup_start_ns, setup_end_ns = timings.get(("setup", 0), (None, None))
    setup_completed = setup_start_ns is not None and setup_end_ns is not None
    setup_returncode = batched_section_returncode(result.returncode, setup_completed)
    setup_elapsed = (
        max(0.0, (setup_end_ns - setup_start_ns) / 1_000_000_000.0)
        if setup_completed and setup_end_ns >= setup_start_ns
        else 0.0
    )
    setup_event = timed_event_from_ns(
        case=case,
        target=target,
        command="setup",
        repeat_idx=0,
        start_ns=setup_start_ns,
        end_ns=setup_end_ns,
        fallback_started_at=started_at,
        fallback_elapsed=setup_elapsed,
        timeout_s=timeout_s,
        returncode=setup_returncode,
        batch_elapsed=batch_elapsed,
    )
    out["setup_event"] = setup_event
    out["command_events"].append(setup_event)
    grouped: dict[str, list[tuple[int, CmdResult, dict[str, Any]]]] = {name: [] for name in commands}
    section_count = max(1, len(sections))
    fallback_section_elapsed = batch_elapsed / section_count
    for name, repeat_idx, _start, _command in sections:
        section_key = (name, repeat_idx)
        section_stdout = parsed.get(section_key, "")
        section_returncode = batched_section_returncode(result.returncode, section_key in parsed)
        section_stderr = result.stderr if section_returncode != 0 else ""
        start_ns, end_ns = timings.get((name, repeat_idx), (None, None))
        section_elapsed = (
            max(0.0, (end_ns - start_ns) / 1_000_000_000.0)
            if start_ns is not None and end_ns is not None and end_ns >= start_ns
            else fallback_section_elapsed
        )
        section_started_at = (
            start_ns / 1_000_000_000.0 if start_ns is not None else started_at
        )
        section_ended_at = (
            end_ns / 1_000_000_000.0
            if end_ns is not None
            else section_started_at + section_elapsed
        )
        section_result = CmdResult(
            returncode=section_returncode,
            stdout=section_stdout,
            stderr=section_stderr,
            elapsed_s=section_elapsed,
        )
        event = timed_event_from_ns(
            case=case,
            target=target,
            command=name,
            repeat_idx=repeat_idx,
            start_ns=start_ns,
            end_ns=end_ns,
            fallback_started_at=section_started_at,
            fallback_elapsed=section_elapsed,
            timeout_s=timeout_s,
            returncode=section_returncode,
            batch_elapsed=batch_elapsed,
        )
        grouped[name].append((repeat_idx, section_result, event))
        out["command_events"].append(event)

    for name in commands:
        runs = [item[1] for item in grouped[name]]
        events = [item[2] for item in grouped[name]]
        entry = command_summary(
            name,
            runs[0],
            include_sensitive,
            case=case,
            target=target,
            gold_manifest=gold_manifest,
        )
        entry["execution_mode"] = "batched"
        entry["batch_elapsed_s"] = round(batch_elapsed, 6)
        if events:
            entry["event"] = events[0]
        if len(runs) > 1:
            hashes = [hashlib.sha256(run.stdout.encode("utf-8", "replace")).hexdigest() for run in runs]
            entry["repeat"] = {
                "count": len(runs),
                "stable": len(set(hashes)) == 1,
                "hashes": hashes,
                "events": events,
            }
        out["commands"][name] = entry
    return annotate_attribution(out, "target")


def command_entry_reusable_for_resume(entry: Any) -> bool:
    if not isinstance(entry, dict):
        return False
    if entry.get("skipped") is True:
        return False
    if section_status_incomplete(entry.get("section_status")):
        return False
    return "returncode" in entry and not command_entry_timed_out(entry)


def target_resume_key(target: dict[str, Any]) -> str:
    addr = target.get("addr")
    if isinstance(addr, int):
        return f"addr:0x{addr:x}"
    name = target.get("name") or target.get("requested") or ""
    return f"name:{normalize_symbol(str(name))}"


def cached_targets_by_resume_key(cached_case: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if not isinstance(cached_case, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for target in cached_case.get("targets", []):
        if isinstance(target, dict):
            out[target_resume_key(target)] = target
    return out


def command_events_from_entry(entry: dict[str, Any]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    event = entry.get("event")
    if isinstance(event, dict):
        events.append(copy.deepcopy(event))
    repeat = entry.get("repeat")
    repeat_events = repeat.get("events") if isinstance(repeat, dict) else None
    if isinstance(repeat_events, list):
        events.extend(copy.deepcopy(event) for event in repeat_events if isinstance(event, dict))
    return events


def attach_cached_target_commands(
    targets: list[dict[str, Any]],
    cached_case: dict[str, Any] | None,
    commands: dict[str, str],
) -> list[dict[str, Any]]:
    cached_targets = cached_targets_by_resume_key(cached_case)
    if not cached_targets:
        return targets
    out: list[dict[str, Any]] = []
    for target in targets:
        resumed_target = dict(target)
        cached_target = cached_targets.get(target_resume_key(target))
        resume_commands: dict[str, dict[str, Any]] = {}
        if isinstance(cached_target, dict):
            cached_commands = cached_target.get("commands")
            if isinstance(cached_commands, dict):
                for name in commands:
                    entry = cached_commands.get(name)
                    if command_entry_reusable_for_resume(entry):
                        resume_commands[name] = copy.deepcopy(entry)
        if resume_commands:
            resumed_target["_resume_commands"] = resume_commands
            resumed_target["_resume_source"] = "target_command_checkpoint"
        out.append(resumed_target)
    return out


def resumed_command_names(target: dict[str, Any]) -> set[str]:
    resume_commands = target.get("_resume_commands")
    if not isinstance(resume_commands, dict):
        return set()
    return {name for name in resume_commands if isinstance(name, str)}


def scheduled_commands_for_target(
    target: dict[str, Any],
    commands: dict[str, str],
) -> dict[str, str]:
    already_done = resumed_command_names(target)
    return {name: command for name, command in commands.items() if name not in already_done}


def public_target_fields(target: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in target.items() if not str(key).startswith("_")}


def target_output_with_resumed_commands(
    target: dict[str, Any],
    commands: dict[str, str],
) -> dict[str, Any]:
    out = public_target_fields(target)
    resume_commands = target.get("_resume_commands")
    out["commands"] = {}
    out["command_events"] = []
    if isinstance(resume_commands, dict):
        for name in commands:
            entry = resume_commands.get(name)
            if isinstance(entry, dict):
                resumed_entry = copy.deepcopy(entry)
                resumed_entry["resumed_from_checkpoint"] = True
                out["commands"][name] = resumed_entry
                out["command_events"].extend(command_events_from_entry(resumed_entry))
    if out["commands"]:
        out["execution_mode"] = "resumed_checkpoint"
        out["attribution_mode"] = "resumed_checkpoint"
        out["resumed_commands"] = list(out["commands"])
    return out


def collect_targets_batched_case(
    r2: str,
    case: BinaryCase,
    targets: list[dict[str, Any]],
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    task_tmpdir: Path | None,
    runner: Runner,
    commands: dict[str, str] | None = None,
    gold_manifest: list[dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    commands = commands or target_commands()
    found_targets = [
        (idx, target)
        for idx, target in enumerate(targets)
        if target.get("found", True) and scheduled_commands_for_target(target, commands)
    ]
    if not found_targets:
        return [target_output_with_resumed_commands(target, commands) for target in targets], []

    command_parts = [
        f"?e {batched_time_marker('START', 'case_setup', 0)}",
        "!date +%s%N",
        case.analysis,
        f"?e {batched_time_marker('END', 'case_setup', 0)}",
        "!date +%s%N",
    ]
    section_specs: list[tuple[int, str, int, str]] = []
    for target_idx, target in found_targets:
        addr = int(target["addr"])
        setup_name = target_setup_name(target_idx)
        command_parts.extend(
            [
                f"?e {batched_time_marker('START', setup_name, 0)}",
                "!date +%s%N",
                f"s 0x{addr:x}; af",
                f"?e {batched_time_marker('END', setup_name, 0)}",
                "!date +%s%N",
            ]
        )
        for command_name, command in scheduled_commands_for_target(target, commands).items():
            per_command_repeats = max(1, repeat) if command_name in DECOMPILE_REPEAT_COMMANDS else 1
            encoded_name = target_section_name(target_idx, command_name)
            for repeat_idx in range(per_command_repeats):
                section_specs.append((target_idx, command_name, repeat_idx, encoded_name))
                command_parts.extend(
                    [
                        f"?e {batched_time_marker('START', encoded_name, repeat_idx)}",
                        "!date +%s%N",
                        f"?e {batched_section_start(encoded_name, repeat_idx)}",
                        command,
                        f"?e {batched_section_end(encoded_name, repeat_idx)}",
                        f"?e {batched_time_marker('END', encoded_name, repeat_idx)}",
                        "!date +%s%N",
                    ]
                )

    command_env = task_env(env, task_tmpdir, case.corpus, case.name, "case-batched")
    started_at = time.time()
    # Keep --timeout as an actual subprocess wall-clock cap. A batched case
    # already trades observability for lower startup cost; scaling by target
    # count can turn one hot function into a many-minute silent benchmark stall.
    batch_timeout_s = timeout_s
    result = runner(r2, case.path, "; ".join(command_parts), batch_timeout_s, command_env)
    ended_at = time.time()
    parsed, timings, started_sections, completed_sections = parse_batched_output_detailed(
        result.stdout
    )
    batch_elapsed = max(0.0, ended_at - started_at)
    case_start_ns, case_end_ns = timings.get(("case_setup", 0), (None, None))
    case_setup_status = setup_section_status(
        start_ns=case_start_ns,
        end_ns=case_end_ns,
        batch_returncode=result.returncode,
    )
    case_setup_returncode = returncode_for_section_status(result.returncode, case_setup_status)
    case_setup_event = {
        "case": case.name,
        "corpus": case.corpus,
        "target": None,
        "addr": None,
        "command": "case_setup",
        "repeat_idx": 0,
        "started_at": round(
            case_start_ns / 1_000_000_000.0 if case_start_ns is not None else started_at,
            6,
        ),
        "ended_at": round(
            case_end_ns / 1_000_000_000.0
            if case_end_ns is not None
            else started_at,
            6,
        ),
        "elapsed_s": round(
            max(0.0, (case_end_ns - case_start_ns) / 1_000_000_000.0)
            if case_start_ns is not None and case_end_ns is not None and case_end_ns >= case_start_ns
            else 0.0,
            6,
        ),
        "timeout_s": batch_timeout_s,
        "timeout": case_setup_returncode == 124,
        "returncode": case_setup_returncode,
        "batch_elapsed_s": round(batch_elapsed, 6),
        "timed": case_start_ns is not None and case_end_ns is not None,
        "section_status": case_setup_status,
    }

    target_setup_statuses: dict[int, str] = {}
    case_setup_blocks_targets = (
        case_setup_status != BATCH_SECTION_COMPLETED
        and result.returncode != 0
        and not started_sections
        and not any(key != ("case_setup", 0) for key in timings)
    )
    for target_idx, _target in found_targets:
        setup_name = target_setup_name(target_idx)
        setup_start_ns, setup_end_ns = timings.get((setup_name, 0), (None, None))
        target_setup_statuses[target_idx] = setup_section_status(
            start_ns=setup_start_ns,
            end_ns=setup_end_ns,
            batch_returncode=result.returncode,
            blocked_by_setup=case_setup_blocks_targets,
        )

    grouped: dict[int, dict[str, list[tuple[int, CmdResult, dict[str, Any]]]]] = {
        idx: {name: [] for name in scheduled_commands_for_target(target, commands)}
        for idx, target in found_targets
    }
    section_count = max(1, len(section_specs))
    fallback_section_elapsed = batch_elapsed / section_count
    for target_idx, command_name, repeat_idx, encoded_name in section_specs:
        section_key = (encoded_name, repeat_idx)
        start_ns, end_ns = timings.get((encoded_name, repeat_idx), (None, None))
        section_status = batched_section_status(
            key=section_key,
            timings=timings,
            started_sections=started_sections,
            completed_sections=completed_sections,
            batch_returncode=result.returncode,
            blocked_by_setup=target_setup_statuses.get(target_idx)
            in {
                BATCH_SECTION_STARTED_TIMEOUT,
                BATCH_SECTION_STARTED_FAILED,
                BATCH_SECTION_SETUP_FAILED,
            },
        )
        section_returncode = returncode_for_section_status(result.returncode, section_status)
        section_stdout = (
            parsed.get(section_key, "")
            if section_status
            in {
                BATCH_SECTION_COMPLETED,
                BATCH_SECTION_STARTED_TIMEOUT,
                BATCH_SECTION_STARTED_FAILED,
            }
            else ""
        )
        section_stderr = result.stderr if section_returncode not in (0, None) else ""
        section_elapsed = (
            max(0.0, (end_ns - start_ns) / 1_000_000_000.0)
            if start_ns is not None and end_ns is not None and end_ns >= start_ns
            else 0.0
            if section_status in INCOMPLETE_SECTION_STATUSES
            else fallback_section_elapsed
        )
        target = targets[target_idx]
        section_result = CmdResult(
            returncode=section_returncode if section_returncode is not None else 0,
            stdout=section_stdout,
            stderr=section_stderr,
            elapsed_s=section_elapsed,
        )
        event = timed_event_from_ns(
            case=case,
            target=target,
            command=command_name,
            repeat_idx=repeat_idx,
            start_ns=start_ns,
            end_ns=end_ns,
            fallback_started_at=started_at,
            fallback_elapsed=section_elapsed,
            timeout_s=timeout_s,
            returncode=section_returncode,
            batch_elapsed=batch_elapsed,
            section_status=section_status,
        )
        grouped[target_idx][command_name].append((repeat_idx, section_result, event))

    outputs: list[dict[str, Any]] = []
    for target_idx, target in enumerate(targets):
        if not target.get("found", True):
            outputs.append(dict(target))
            continue
        out = target_output_with_resumed_commands(target, commands)
        target_scheduled_commands = scheduled_commands_for_target(target, commands)
        if not target_scheduled_commands:
            outputs.append(annotate_attribution(out, "resumed_checkpoint"))
            continue
        out["execution_mode"] = "batched"
        out.setdefault("commands", {})
        out.setdefault("command_events", [])
        out["batch_event"] = {
            "case": case.name,
            "corpus": case.corpus,
            "target": target.get("name") or target.get("requested"),
            "addr": target.get("addr"),
            "command": "case_batch",
            "repeat_idx": 0,
            "started_at": round(started_at, 6),
            "ended_at": round(ended_at, 6),
            "elapsed_s": round(batch_elapsed, 6),
            "timeout_s": batch_timeout_s,
            "timeout": result.returncode == 124,
            "returncode": result.returncode,
        }
        setup_name = target_setup_name(target_idx)
        setup_start_ns, setup_end_ns = timings.get((setup_name, 0), (None, None))
        setup_status = target_setup_statuses.get(target_idx, BATCH_SECTION_NOT_REACHED)
        setup_returncode = returncode_for_section_status(result.returncode, setup_status)
        setup_event = timed_event_from_ns(
            case=case,
            target=target,
            command="setup",
            repeat_idx=0,
            start_ns=setup_start_ns,
            end_ns=setup_end_ns,
            fallback_started_at=started_at,
            fallback_elapsed=0.0,
            timeout_s=timeout_s,
            returncode=setup_returncode,
            batch_elapsed=batch_elapsed,
            section_status=setup_status,
        )
        out["setup_event"] = setup_event
        out["command_events"].append(setup_event)
        for command_name in target_scheduled_commands:
            runs = [item[1] for item in grouped[target_idx][command_name]]
            events = [item[2] for item in grouped[target_idx][command_name]]
            if events and any(section_status_incomplete(event.get("section_status")) for event in events):
                entry = skipped_command_summary(
                    command_name,
                    str(events[0].get("section_status") or BATCH_SECTION_NOT_REACHED),
                    events[0],
                    include_sensitive,
                )
            else:
                entry = command_summary(
                    command_name,
                    runs[0],
                    include_sensitive,
                    case=case,
                    target=target,
                    gold_manifest=gold_manifest,
                )
            entry["execution_mode"] = "batched"
            entry["batch_elapsed_s"] = round(batch_elapsed, 6)
            if events:
                entry["event"] = events[0]
                entry["section_status"] = events[0].get("section_status")
                out["command_events"].extend(events)
            if len(runs) > 1:
                hashes = [hashlib.sha256(run.stdout.encode("utf-8", "replace")).hexdigest() for run in runs]
                entry["repeat"] = {
                    "count": len(runs),
                    "stable": len(set(hashes)) == 1,
                    "hashes": hashes,
                    "events": events,
                }
            out["commands"][command_name] = entry
        outputs.append(annotate_attribution(out, "batch"))
    return outputs, [case_setup_event]


def collect_target_command_retries(
    r2: str,
    case: BinaryCase,
    target: dict[str, Any],
    base_output: dict[str, Any],
    command_names: set[str],
    commands: dict[str, str],
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    task_tmpdir: Path | None,
    jobs: int,
    runner: Runner,
    *,
    retry_origin: str,
    gold_manifest: list[dict[str, Any]] | None = None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if not target.get("found", True) or not command_names:
        return base_output, []

    addr = int(target["addr"])
    prefix = f"{case.analysis}; s 0x{addr:x}; af"
    selected_names = [name for name in commands if name in command_names]
    if not selected_names:
        return base_output, []

    out: dict[str, Any] = copy.deepcopy(base_output)
    out["execution_mode"] = "batched_with_command_retry"
    out["attribution_mode"] = "batch_with_command_retry"
    out["retry_origin"] = retry_origin
    out["retry_commands"] = selected_names
    out.setdefault("commands", {})
    out["command_events"] = list(out.get("command_events", []))
    repeat_count = max(1, repeat)

    command_runs: list[tuple[str, int, str]] = []
    for name in selected_names:
        command = commands[name]
        per_command_repeats = repeat_count if name in DECOMPILE_REPEAT_COMMANDS else 1
        for repeat_idx in range(per_command_repeats):
            command_runs.append((name, repeat_idx, command))

    def run_command(spec: tuple[str, int, str]) -> tuple[str, int, CmdResult, dict[str, Any]]:
        name, repeat_idx, command = spec
        command_env = task_env(
            env,
            task_tmpdir,
            case.corpus,
            case.name,
            f"target-0x{addr:x}",
            "command-retry",
            name,
            f"run-{repeat_idx}",
        )
        started_at = time.time()
        result = runner(r2, case.path, f"{prefix}; {command}", timeout_s, command_env)
        ended_at = time.time()
        event = command_event(
            case=case,
            target=target,
            command=name,
            repeat_idx=repeat_idx,
            started_at=started_at,
            ended_at=ended_at,
            timeout_s=timeout_s,
            returncode=result.returncode,
        )
        event["attribution_mode"] = "command_retry"
        event["retry_origin"] = retry_origin
        return name, repeat_idx, result, event

    completed = run_ordered_parallel(command_runs, jobs, run_command)
    runs_by_command: dict[str, list[CmdResult]] = {name: [] for name in selected_names}
    events_by_command: dict[str, list[dict[str, Any]]] = {name: [] for name in selected_names}
    retry_events: list[dict[str, Any]] = []
    for name, _repeat_idx, result, event in completed:
        runs_by_command[name].append(result)
        events_by_command[name].append(event)
        retry_events.append(event)
        out["command_events"].append(event)

    for name in selected_names:
        runs = runs_by_command[name]
        if not runs:
            continue
        old_entry = out.get("commands", {}).get(name)
        entry = command_summary(
            name,
            runs[0],
            include_sensitive,
            case=case,
            target=target,
            gold_manifest=gold_manifest,
        )
        entry["execution_mode"] = "isolated_retry"
        entry["attribution_mode"] = "command_retry"
        entry["retry_origin"] = retry_origin
        if isinstance(old_entry, dict):
            entry["retry_replaced"] = {
                "execution_mode": old_entry.get("execution_mode"),
                "attribution_mode": old_entry.get("attribution_mode"),
                "timeout": bool(old_entry.get("timeout")),
                "returncode": old_entry.get("returncode"),
            }
        events = events_by_command[name]
        if events:
            entry["event"] = events[0]
        if len(runs) > 1:
            hashes = [hashlib.sha256(run.stdout.encode("utf-8", "replace")).hexdigest() for run in runs]
            entry["repeat"] = {
                "count": len(runs),
                "stable": len(set(hashes)) == 1,
                "hashes": hashes,
                "events": events,
            }
        out["commands"][name] = entry

    return out, retry_events


def collect_targets_batched_adaptive(
    r2: str,
    case: BinaryCase,
    targets: list[dict[str, Any]],
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    task_tmpdir: Path | None,
    command_jobs: int,
    runner: Runner,
    commands: dict[str, str] | None = None,
    gold_manifest: list[dict[str, Any]] | None = None,
    *,
    depth: int = 0,
    retry_origin: str | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    commands = commands or target_commands()
    outputs, events = collect_targets_batched_case(
        r2,
        case,
        targets,
        timeout_s,
        repeat,
        include_sensitive,
        env,
        task_tmpdir,
        runner,
        commands,
        gold_manifest,
    )
    mode = "batch" if depth == 0 else "batch_retry"
    for output in outputs:
        annotate_attribution(output, mode, retry_origin=retry_origin)
    for event in events:
        event["attribution_mode"] = mode
        if retry_origin:
            event["retry_origin"] = retry_origin

    retry_indices = [
        idx for idx, output in enumerate(outputs) if target_has_retryable_command(output)
    ]
    if not retry_indices:
        return outputs, events

    for retry_idx in retry_indices:
        retry_target = targets[retry_idx]
        timed_out = target_has_timed_out_command(outputs[retry_idx])
        command_names = (
            timed_out_command_names(outputs[retry_idx])
            if timed_out
            else retryable_command_names(outputs[retry_idx])
        )
        command_tmpdir = (
            task_tmpdir.joinpath(f"retry-{depth}-commands-{retry_idx}")
            if task_tmpdir is not None
            else None
        )
        origin = "batch_timeout" if timed_out else "batch_failure"
        retry_output, retry_events = collect_target_command_retries(
            r2,
            case,
            retry_target,
            outputs[retry_idx],
            command_names,
            commands,
            timeout_s,
            repeat,
            include_sensitive,
            env,
            command_tmpdir,
            command_jobs,
            runner,
            retry_origin=retry_origin or origin,
            gold_manifest=gold_manifest,
        )
        outputs[retry_idx] = retry_output
        events.extend(retry_events)
    return outputs, events


def collect_target(
    r2: str,
    case: BinaryCase,
    target: dict[str, Any],
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    task_tmpdir: Path | None,
    jobs: int,
    runner: Runner,
    commands: dict[str, str] | None = None,
    gold_manifest: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    if not target.get("found", True):
        return dict(target)
    commands = commands or target_commands()
    addr = int(target["addr"])
    prefix = f"{case.analysis}; s 0x{addr:x}; af"
    out = target_output_with_resumed_commands(target, commands)
    out["execution_mode"] = "isolated"
    out.setdefault("commands", {})
    repeat_count = max(1, repeat)
    commands_to_run = scheduled_commands_for_target(target, commands)
    if not commands_to_run:
        return annotate_attribution(out, "resumed_checkpoint")

    command_runs: list[tuple[str, int, str]] = []
    for name, command in commands_to_run.items():
        per_command_repeats = repeat_count if name in DECOMPILE_REPEAT_COMMANDS else 1
        for repeat_idx in range(per_command_repeats):
            command_runs.append((name, repeat_idx, command))

    def run_command(spec: tuple[str, int, str]) -> tuple[str, int, CmdResult, dict[str, Any]]:
        name, repeat_idx, command = spec
        command_env = task_env(
            env,
            task_tmpdir,
            case.corpus,
            case.name,
            f"target-0x{addr:x}",
            name,
            f"run-{repeat_idx}",
        )
        started_at = time.time()
        result = runner(r2, case.path, f"{prefix}; {command}", timeout_s, command_env)
        ended_at = time.time()
        return (
            name,
            repeat_idx,
            result,
            command_event(
                case=case,
                target=target,
                command=name,
                repeat_idx=repeat_idx,
                started_at=started_at,
                ended_at=ended_at,
                timeout_s=timeout_s,
                returncode=result.returncode,
            ),
        )

    completed = run_ordered_parallel(command_runs, jobs, run_command)
    runs_by_command: dict[str, list[CmdResult]] = {name: [] for name in commands_to_run}
    events_by_command: dict[str, list[dict[str, Any]]] = {name: [] for name in commands_to_run}
    out.setdefault("command_events", [])
    for name, _repeat_idx, result, event in completed:
        runs_by_command[name].append(result)
        events_by_command[name].append(event)
        out["command_events"].append(event)

    for name in commands_to_run:
        runs = runs_by_command[name]
        entry = command_summary(
            name,
            runs[0],
            include_sensitive,
            case=case,
            target=target,
            gold_manifest=gold_manifest,
        )
        events = events_by_command[name]
        if events:
            entry["event"] = events[0]
        if len(runs) > 1:
            hashes = [hashlib.sha256(run.stdout.encode("utf-8", "replace")).hexdigest() for run in runs]
            entry["repeat"] = {
                "count": len(runs),
                "stable": len(set(hashes)) == 1,
                "hashes": hashes,
                "events": events,
            }
        out["commands"][name] = entry
    return annotate_attribution(out, "command")


def _quality_gate_result_ready(result: dict[str, Any]) -> bool:
    if result.get("skipped") is True:
        return False
    if bool(result.get("timeout")) or bool(
        isinstance(result.get("event"), dict) and result["event"].get("timeout")
    ):
        return False
    returncode = result.get("returncode")
    if returncode is not None and returncode != 0:
        return False
    return isinstance(result.get("decompile_quality"), dict)


def _type_metric_signature(types_entry: Any) -> tuple[str | None, int | None]:
    if not isinstance(types_entry, dict):
        return None, None
    metrics = types_entry.get("type_metrics")
    if not isinstance(metrics, dict):
        return None, None
    ret_type = metrics.get("ret_type")
    param_count = metrics.get("param_count")
    return (
        ret_type if isinstance(ret_type, str) else None,
        param_count if isinstance(param_count, int) and not isinstance(param_count, bool) else None,
    )


def quality_gate_failures_for_result(
    target_name: Any,
    command: str,
    result: dict[str, Any],
    commands: dict[str, Any],
) -> list[dict[str, Any]]:
    if command in BASELINE_COMMANDS or not command.startswith(DECOMPILE_COMMAND_PREFIX):
        return []
    if not _quality_gate_result_ready(result):
        return []

    quality = result.get("decompile_quality")
    if not isinstance(quality, dict):
        return []

    failures: list[dict[str, Any]] = []

    def add(kind: str, **extra: Any) -> None:
        failures.append({"kind": kind, "target": target_name, "command": command, **extra})

    comment_only = bool(quality.get("comment_only"))
    if int(quality.get("argn_leak_count") or 0) > 0:
        add("argn_leak", count=int(quality.get("argn_leak_count") or 0))
    if comment_only:
        add("comment_only_decompile")
    if int(quality.get("fake_while_break_wrapper_count") or 0) > 0:
        add(
            "fake_while_break_wrapper",
            count=int(quality.get("fake_while_break_wrapper_count") or 0),
        )
    if int(quality.get("empty_loop_body_count") or 0) > 0:
        add(
            "empty_loop_body",
            count=int(quality.get("empty_loop_body_count") or 0),
        )
    if int(quality.get("summary_pseudo_call_count") or 0) > 0:
        add(
            "summary_pseudo_call",
            count=int(quality.get("summary_pseudo_call_count") or 0),
        )
    if int(quality.get("undefined_identifier_return_count") or 0) > 0:
        add(
            "undefined_identifier_return",
            count=int(quality.get("undefined_identifier_return_count") or 0),
        )
    if bool(quality.get("missing_return_nonvoid")) and not comment_only:
        add("missing_return_nonvoid", header_ret_type=quality.get("header_ret_type"))
    if (
        int(quality.get("unresolved_fcn_count") or 0) > 0
        or int(quality.get("artifact_count") or 0) > 0
        or int(quality.get("raw_temp_stack_leak_count") or 0) > 0
        or int(quality.get("stack_address_leak_count") or 0) > 0
    ):
        add(
            "unresolved_fcn_or_temp_stack_leak",
            unresolved_fcn_count=int(quality.get("unresolved_fcn_count") or 0),
            artifact_count=int(quality.get("artifact_count") or 0),
            raw_temp_stack_leak_count=int(quality.get("raw_temp_stack_leak_count") or 0),
            stack_address_leak_count=int(quality.get("stack_address_leak_count") or 0),
        )

    type_ret, type_params = _type_metric_signature(commands.get("types"))
    header_ret = quality.get("header_ret_type")
    header_params = quality.get("header_param_count")
    if isinstance(header_ret, str) and type_ret:
        if is_void_type(header_ret) != is_void_type(type_ret):
            add(
                "decompile_header_return_mismatch",
                types_ret_type=type_ret,
                decompile_ret_type=header_ret,
            )
        elif _normalized_c_type(header_ret) != _normalized_c_type(type_ret):
            add(
                "decompile_header_signature_mismatch",
                reason="return type differs",
                types_ret_type=type_ret,
                decompile_ret_type=header_ret,
            )
    if isinstance(header_params, int) and type_params is not None and header_params != type_params:
        add(
            "decompile_header_signature_mismatch",
            reason="parameter count differs",
            types_param_count=type_params,
            decompile_param_count=header_params,
        )
    return failures


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
        alias = target.get("target_alias")
        if isinstance(alias, dict) and isinstance(alias.get("kind"), str):
            failures.append(
                {
                    "kind": alias["kind"],
                    "target": alias.get("requested") or target.get("requested") or target_name,
                    "matched": alias.get("matched") or target.get("name"),
                    "requested_prefix": alias.get("requested_prefix"),
                    "matched_prefix": alias.get("matched_prefix"),
                }
            )
        commands = target.get("commands", {})
        if not isinstance(commands, dict):
            continue
        for command, result in commands.items():
            if not isinstance(result, dict):
                continue
            if command in BASELINE_COMMANDS:
                continue
            if result.get("skipped") is True:
                continue
            timed_out = bool(result.get("timeout")) or bool(
                isinstance(result.get("event"), dict) and result["event"].get("timeout")
            )
            if timed_out:
                failures.append({"kind": "timeout", "target": target_name, "command": command})
                continue
            if result.get("returncode") is not None and result.get("returncode") != 0:
                failures.append({"kind": "command_return", "target": target_name, "command": command})
            if result.get("json_error"):
                failures.append({"kind": "json_parse", "target": target_name, "command": command})
            if result.get("empty") is True:
                failures.append({"kind": "empty_decompile", "target": target_name, "command": command})
            if result.get("fallback_marker"):
                failures.append({"kind": "decompiler_fallback", "target": target_name, "command": command})
            gold_oracle = result.get("gold_oracle")
            if isinstance(gold_oracle, dict):
                for failure in gold_oracle.get("failures", []):
                    if isinstance(failure, dict):
                        failures.append(dict(failure))
            repeat = result.get("repeat")
            if isinstance(repeat, dict) and repeat.get("stable") is False:
                failures.append({"kind": "nondeterministic_output", "target": target_name, "command": command})
            failures.extend(
                quality_gate_failures_for_result(target_name, command, result, commands)
            )
    failures.sort(key=lambda item: (item.get("kind", ""), item.get("target", ""), item.get("command", "")))
    return failures
def add_cache_counter_totals(dest: dict[str, int], source: dict[str, Any]) -> None:
    for field in CACHE_COUNTER_FIELDS:
        value = source.get(field)
        if isinstance(value, int) and not isinstance(value, bool):
            dest[field] = dest.get(field, 0) + value


def add_engine_cache_totals(
    dest: dict[str, dict[str, int]], source: dict[str, Any]
) -> None:
    for partition in ("analysis", "artifacts", "renders", "total"):
        counters = source.get(partition)
        if isinstance(counters, dict):
            add_cache_counter_totals(dest.setdefault(partition, {}), counters)


def cache_total_name(name: str) -> str:
    aliases = {
        "decompile_cache": "decompile",
        "summary_cache": "summary",
        "engine_cache": "engine",
    }
    if name in aliases:
        return aliases[name]
    if name.endswith("_cache"):
        return name[: -len("_cache")]
    return name


def add_cache_metrics_totals(
    engine_dest: dict[str, dict[str, int]],
    cache_dest: dict[str, dict[str, int]],
    source: dict[str, Any],
) -> None:
    for name, metrics in source.items():
        if not isinstance(name, str) or not isinstance(metrics, dict):
            continue
        if name == "engine_cache":
            add_engine_cache_totals(engine_dest, metrics)
            continue
        add_cache_counter_totals(cache_dest.setdefault(cache_total_name(name), {}), metrics)


def fast_path_totals_template() -> dict[str, Any]:
    return {
        "summary_fast_path_count": 0,
        "summary_only_count": 0,
        "cache_hit_commands": 0,
        "semantic_granularity": {},
        "phase_timings_us": {},
        "counters": {},
    }


def add_fast_path_totals(dest: dict[str, Any], source: dict[str, Any]) -> None:
    if source.get("summary_fast_path") is True:
        dest["summary_fast_path_count"] += 1
    if source.get("summary_only") is True:
        dest["summary_only_count"] += 1
    if source.get("cache_hit") is True:
        dest["cache_hit_commands"] += 1
    granularity = source.get("semantic_granularity")
    if isinstance(granularity, str) and granularity:
        buckets = dest["semantic_granularity"]
        buckets[granularity] = buckets.get(granularity, 0) + 1
    phase_timings = source.get("phase_timings_us")
    if isinstance(phase_timings, dict):
        totals = dest["phase_timings_us"]
        for phase, elapsed in phase_timings.items():
            if isinstance(phase, str) and isinstance(elapsed, int) and not isinstance(elapsed, bool):
                totals[phase] = totals.get(phase, 0) + elapsed
    counters = dest["counters"]
    for field in FAST_PATH_COUNTER_FIELDS + SEMANTIC_SUMMARY_COUNT_FIELDS:
        value = source.get(field)
        if isinstance(value, int) and not isinstance(value, bool):
            counters[field] = counters.get(field, 0) + value


def finalized_fast_path_totals(totals: dict[str, Any]) -> dict[str, Any]:
    return {
        "summary_fast_path_count": totals["summary_fast_path_count"],
        "summary_only_count": totals["summary_only_count"],
        "cache_hit_commands": totals["cache_hit_commands"],
        "semantic_granularity": dict(sorted(totals["semantic_granularity"].items())),
        "phase_timings_us": dict(sorted(totals["phase_timings_us"].items())),
        "counters": dict(sorted(totals["counters"].items())),
    }


def score_case(case_result: dict[str, Any]) -> int:
    penalty_by_kind = {
        "discovery_return": 25,
        "discovery_parse": 20,
        "zero_functions": 20,
        "missing_target": 15,
        "missing_debug_target_alias": 3,
        "missing_symbol_target_alias": 3,
        "missing_symbol_debug_target_alias": 3,
        "command_return": 10,
        "empty_decompile": 10,
        "decompiler_fallback": 10,
        "json_parse": 5,
        "nondeterministic_output": 10,
        "radare2_candidate": 8,
        "timeout": 10,
        "argn_leak": 6,
        "comment_only_decompile": 12,
        "decompile_header_return_mismatch": 12,
        "decompile_header_signature_mismatch": 8,
        "fake_while_break_wrapper": 10,
        "missing_return_nonvoid": 10,
        "summary_pseudo_call": 8,
        "undefined_identifier_return": 12,
        GOLD_ORACLE_FAILURE: 15,
        "unresolved_fcn_or_temp_stack_leak": 8,
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


def _float_value(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _quality_rank(entry: dict[str, Any]) -> int:
    quality = entry.get("decompile_quality")
    if not isinstance(quality, dict):
        return QUALITY_RANK["empty"]
    classification = str(quality.get("classification") or "empty")
    return QUALITY_RANK.get(classification, QUALITY_RANK["empty"])


def _quality_score(entry: dict[str, Any]) -> int:
    quality = entry.get("decompile_quality")
    if not isinstance(quality, dict):
        return QUALITY_RANK["empty"] * 100
    return (
        _quality_rank(entry) * 100
        - int(quality.get("source_smell_count") or 0) * 10
        - int(quality.get("readability_smell_count") or 0) * 3
        - int(quality.get("pointer_cast_count") or 0) * 2
        - int(quality.get("control_flow_noise_count") or 0) * 5
        - int(quality.get("synthetic_type_leak_count") or 0) * 8
        - int(quality.get("artifact_count") or 0)
    )


def _command_success(entry: dict[str, Any]) -> bool:
    if entry.get("skipped") or entry.get("timeout"):
        return False
    returncode = entry.get("returncode")
    if returncode not in (None, 0):
        return False
    section_status = entry.get("section_status")
    if section_status is not None and section_status != BATCH_SECTION_COMPLETED:
        return False
    return True


def pdg_target_comparison(case: dict[str, Any], target: dict[str, Any]) -> dict[str, Any] | None:
    commands = target.get("commands")
    if not isinstance(commands, dict):
        return None
    sla = commands.get("decompile_sla")
    pdg = commands.get("decompile_pdg")
    if not isinstance(sla, dict) or not isinstance(pdg, dict):
        return None
    sla_quality = sla.get("decompile_quality") if isinstance(sla.get("decompile_quality"), dict) else {}
    pdg_quality = pdg.get("decompile_quality") if isinstance(pdg.get("decompile_quality"), dict) else {}
    sla_success = _command_success(sla)
    pdg_success = _command_success(pdg)
    comparable = sla_success and pdg_success
    sla_rank = _quality_rank(sla)
    pdg_rank = _quality_rank(pdg)
    sla_score = _quality_score(sla)
    pdg_score = _quality_score(pdg)
    sla_elapsed = _float_value(sla.get("elapsed_s"))
    pdg_elapsed = _float_value(pdg.get("elapsed_s"))
    elapsed_delta = round(sla_elapsed - pdg_elapsed, 6)
    speedup = round(pdg_elapsed / sla_elapsed, 6) if sla_elapsed > 0.0 else None
    return {
        "case": case.get("name"),
        "corpus": case.get("corpus"),
        "target": target.get("name") or target.get("requested"),
        "comparable": comparable,
        "sla_success": sla_success,
        "pdg_success": pdg_success,
        "sla_returncode": sla.get("returncode"),
        "pdg_returncode": pdg.get("returncode"),
        "sla_section_status": sla.get("section_status"),
        "pdg_section_status": pdg.get("section_status"),
        "sla_classification": sla_quality.get("classification"),
        "pdg_classification": pdg_quality.get("classification"),
        "classification_delta": sla_rank - pdg_rank if comparable else None,
        "quality_delta": sla_score - pdg_score if comparable else None,
        "sla_quality_score": sla_score if comparable else None,
        "pdg_quality_score": pdg_score if comparable else None,
        "sla_source_smells": int(sla_quality.get("source_smell_count") or 0),
        "pdg_source_smells": int(pdg_quality.get("source_smell_count") or 0),
        "sla_readability_smells": int(sla_quality.get("readability_smell_count") or 0),
        "pdg_readability_smells": int(pdg_quality.get("readability_smell_count") or 0),
        "sla_casts": int(sla_quality.get("cast_expr_count") or 0),
        "pdg_casts": int(pdg_quality.get("cast_expr_count") or 0),
        "sla_pointer_casts": int(sla_quality.get("pointer_cast_count") or 0),
        "pdg_pointer_casts": int(pdg_quality.get("pointer_cast_count") or 0),
        "sla_control_flow_noise": int(sla_quality.get("control_flow_noise_count") or 0),
        "pdg_control_flow_noise": int(pdg_quality.get("control_flow_noise_count") or 0),
        "sla_orphan_breaks": int(sla_quality.get("orphan_break_count") or 0),
        "pdg_orphan_breaks": int(pdg_quality.get("orphan_break_count") or 0),
        "sla_synthetic_type_leaks": int(sla_quality.get("synthetic_type_leak_count") or 0),
        "pdg_synthetic_type_leaks": int(pdg_quality.get("synthetic_type_leak_count") or 0),
        "sla_pointer_scalar_compares": int(sla_quality.get("pointer_scalar_compare_count") or 0),
        "pdg_pointer_scalar_compares": int(pdg_quality.get("pointer_scalar_compare_count") or 0),
        "sla_elapsed_s": round(sla_elapsed, 6),
        "pdg_elapsed_s": round(pdg_elapsed, 6),
        "elapsed_delta_s": elapsed_delta if comparable else None,
        "sla_speedup_vs_pdg": speedup if comparable else None,
        "artifact_delta": (
            int(sla_quality.get("artifact_count") or 0)
            - int(pdg_quality.get("artifact_count") or 0)
            if comparable
            else None
        ),
        "sla_artifact_count": int(sla_quality.get("artifact_count") or 0),
        "pdg_artifact_count": int(pdg_quality.get("artifact_count") or 0),
    }


def _summarize_pdg_counts(comparisons: list[dict[str, Any]]) -> dict[str, Any]:
    quality_counts = {"sla": 0, "pdg": 0, "tie": 0}
    perf_counts = {"sla": 0, "pdg": 0, "tie": 0}
    quality_then_perf_counts = {"sla": 0, "pdg": 0, "tie": 0}
    artifact_counts = {"sla": 0, "pdg": 0, "tie": 0}
    comparable = [item for item in comparisons if item.get("comparable")]
    for item in comparable:
        quality_delta = int(item.get("quality_delta") or 0)
        if quality_delta > 0:
            quality_counts["sla"] += 1
        elif quality_delta < 0:
            quality_counts["pdg"] += 1
        else:
            quality_counts["tie"] += 1

        elapsed_delta = _float_value(item.get("elapsed_delta_s"))
        if elapsed_delta < -0.001:
            perf_counts["sla"] += 1
        elif elapsed_delta > 0.001:
            perf_counts["pdg"] += 1
        else:
            perf_counts["tie"] += 1

        if quality_delta > 0:
            quality_then_perf_counts["sla"] += 1
        elif quality_delta < 0:
            quality_then_perf_counts["pdg"] += 1
        elif elapsed_delta < -0.001:
            quality_then_perf_counts["sla"] += 1
        elif elapsed_delta > 0.001:
            quality_then_perf_counts["pdg"] += 1
        else:
            quality_then_perf_counts["tie"] += 1

        artifact_delta = int(item.get("artifact_delta") or 0)
        if artifact_delta < 0:
            artifact_counts["sla"] += 1
        elif artifact_delta > 0:
            artifact_counts["pdg"] += 1
        else:
            artifact_counts["tie"] += 1

    return {
        "common_targets": len(comparisons),
        "successful_common_targets": len(comparable),
        "sla_failed": sum(1 for item in comparisons if not item.get("sla_success")),
        "pdg_failed": sum(1 for item in comparisons if not item.get("pdg_success")),
        "both_failed": sum(
            1
            for item in comparisons
            if not item.get("sla_success") and not item.get("pdg_success")
        ),
        "quality": quality_counts,
        "perf": perf_counts,
        "quality_then_perf": quality_then_perf_counts,
        "artifacts": artifact_counts,
        "sla_both_quality_and_perf_wins": sum(
            1
            for item in comparable
            if int(item.get("quality_delta") or 0) > 0
            and _float_value(item.get("elapsed_delta_s")) < -0.001
        ),
        "pdg_both_quality_and_perf_wins": sum(
            1
            for item in comparable
            if int(item.get("quality_delta") or 0) < 0
            and _float_value(item.get("elapsed_delta_s")) > 0.001
        ),
    }


def _group_pdg_comparisons(
    comparisons: list[dict[str, Any]], key_fn: Callable[[dict[str, Any]], str]
) -> dict[str, dict[str, Any]]:
    groups: dict[str, list[dict[str, Any]]] = {}
    for item in comparisons:
        key = key_fn(item) or "unknown"
        groups.setdefault(key, []).append(item)
    return {key: _summarize_pdg_counts(groups[key]) for key in sorted(groups)}


def summarize_pdg_comparisons(comparisons: list[dict[str, Any]]) -> dict[str, Any]:
    counts = _summarize_pdg_counts(comparisons)
    comparable = [item for item in comparisons if item.get("comparable")]

    worst_quality_gaps = sorted(
        comparable,
        key=lambda item: (
            int(item.get("quality_delta") or 0),
            -_float_value(item.get("elapsed_delta_s")),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
        ),
    )[:10]
    slowest_sla_vs_pdg = sorted(
        comparable,
        key=lambda item: (
            -_float_value(item.get("elapsed_delta_s")),
            int(item.get("quality_delta") or 0),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
        ),
    )[:10]
    failed_targets = sorted(
        [item for item in comparisons if not item.get("comparable")],
        key=lambda item: (
            bool(item.get("sla_success")),
            bool(item.get("pdg_success")),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
        ),
    )[:10]
    counts.update(
        {
            "by_corpus": _group_pdg_comparisons(
                comparisons, lambda item: str(item.get("corpus") or "unknown")
            ),
            "by_family": _group_pdg_comparisons(
                comparisons, lambda item: target_family(str(item.get("target") or ""))
            ),
        }
    )
    counts.update(
        {
            "worst_quality_gaps": worst_quality_gaps,
            "slowest_sla_vs_pdg": slowest_sla_vs_pdg,
            "failed_targets": failed_targets,
        }
    )
    return counts


def _target_examples_for_owner(
    owner: str, target_rollups: list[dict[str, Any]], limit: int = 5
) -> list[dict[str, Any]]:
    examples: list[dict[str, Any]] = []
    for target in target_rollups:
        owner_buckets = target.get("owner_buckets")
        if not isinstance(owner_buckets, dict):
            continue
        count = int(owner_buckets.get(owner) or 0)
        if count <= 0:
            continue
        examples.append(
            {
                "corpus": target.get("corpus"),
                "case": target.get("case"),
                "target": target.get("target"),
                "family": target.get("family"),
                "count": count,
                "hard_failures": int(target.get("hard_failures") or 0),
                "residual_commands": int(target.get("residual_commands") or 0),
                "generic_arg_count": int(target.get("generic_arg_count") or 0),
                "generic_type_count": int(target.get("generic_type_count") or 0),
                "elapsed_s": _float_value(target.get("elapsed_s")),
            }
        )
    examples.sort(
        key=lambda item: (
            -int(item.get("count") or 0),
            -int(item.get("hard_failures") or 0),
            -int(item.get("residual_commands") or 0),
            -int(item.get("generic_arg_count") or 0),
            -int(item.get("generic_type_count") or 0),
            -_float_value(item.get("elapsed_s")),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
        )
    )
    return examples[:limit]


def _owner_work_items(
    owner_buckets: dict[str, int], target_rollups: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    items = []
    for owner, count in sorted(
        owner_buckets.items(), key=lambda item: (-int(item[1]), str(item[0]))
    ):
        items.append(
            {
                "owner": owner,
                "count": int(count),
                "action": OWNER_ACTIONS.get(owner, OWNER_ACTIONS["unknown"]),
                "targets": _target_examples_for_owner(owner, target_rollups),
            }
        )
    return items


def _pdg_next_work(pdg_summary: dict[str, Any]) -> dict[str, Any]:
    common_targets = int(pdg_summary.get("common_targets") or 0)
    successful_common_targets = int(pdg_summary.get("successful_common_targets") or 0)
    quality = pdg_summary.get("quality")
    perf = pdg_summary.get("perf")
    quality_then_perf = pdg_summary.get("quality_then_perf")
    pdg_quality_wins = (
        int(quality.get("pdg") or 0) if isinstance(quality, dict) else 0
    )
    pdg_raw_perf_wins = int(perf.get("pdg") or 0) if isinstance(perf, dict) else 0
    pdg_quality_then_perf_wins = (
        int(quality_then_perf.get("pdg") or 0)
        if isinstance(quality_then_perf, dict)
        else 0
    )
    if common_targets == 0:
        status = "not_run"
    elif pdg_quality_wins or pdg_quality_then_perf_wins:
        status = "quality_gap"
    else:
        status = "ok"
    return {
        "status": status,
        "common_targets": common_targets,
        "successful_common_targets": successful_common_targets,
        "pdg_quality_wins": pdg_quality_wins,
        "pdg_raw_perf_wins": pdg_raw_perf_wins,
        "pdg_quality_then_perf_wins": pdg_quality_then_perf_wins,
    }


def benchmark_next_work(
    owner_buckets: dict[str, int],
    target_rollups: list[dict[str, Any]],
    slow_commands: list[dict[str, Any]],
    timing: dict[str, Any],
    pdg_summary: dict[str, Any],
) -> dict[str, Any]:
    owner_items = _owner_work_items(owner_buckets, target_rollups)
    setup_ratio = timing.get("setup_to_command_ratio")
    setup_ratio_value = (
        round(_float_value(setup_ratio), 6) if setup_ratio is not None else None
    )
    setup_bottleneck = bool(setup_ratio_value is not None and setup_ratio_value > 2.0)
    slow_setup = [
        item
        for item in slow_commands
        if str(item.get("command") or "") in {"case_setup", "setup"}
    ][:5]
    pdg = _pdg_next_work(pdg_summary)
    if owner_items:
        status = "owner_work"
    elif pdg["status"] == "quality_gap":
        status = "pdg_quality_gap"
    elif setup_bottleneck:
        status = "setup_bottleneck"
    else:
        status = "clean"
    return {
        "status": status,
        "blocking_owners": [item["owner"] for item in owner_items],
        "owner_work_items": owner_items,
        "setup": {
            "status": "bottleneck" if setup_bottleneck else "ok",
            "setup_to_command_ratio": setup_ratio_value,
            "max_recommended_ratio": 2.0,
            "slowest_setup_commands": slow_setup,
        },
        "pdg": pdg,
    }


def run_case(
    r2: str,
    case: BinaryCase,
    timeout_s: int,
    repeat: int,
    include_sensitive: bool,
    env: dict[str, str] | None,
    task_tmpdir: Path | None = None,
    jobs: int = 1,
    runner: Runner = run_r2,
    isolate_commands: bool = True,
    batch_target_size: int = 0,
    command_names: tuple[str, ...] | None = None,
    cached_case: dict[str, Any] | None = None,
    gold_manifest: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    started = time.perf_counter()
    commands = target_commands(command_names)
    case_out: dict[str, Any] = {
        "name": case.name,
        "corpus": case.corpus,
        "binary": display_path(case.path, include_sensitive),
        "analysis": case.analysis,
        "requested_targets": list(case.targets),
        "execution_mode": "isolated" if isolate_commands else "batched",
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
        task_env(env, task_tmpdir, case.corpus, case.name, "native-discovery"),
        runner,
        with_plugin=False,
    )
    native_probe = probe_native_pdfj(
        r2,
        case,
        native_functions,
        timeout_s,
        include_sensitive,
        task_env(env, task_tmpdir, case.corpus, case.name, "native-pdfj-probe"),
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

    functions, discovery, discovery_error = discover_functions(
        r2,
        case,
        timeout_s,
        task_env(env, task_tmpdir, case.corpus, case.name, "plugin-discovery"),
        runner,
    )
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
    selected = attach_cached_target_commands(
        choose_targets(functions, case.targets, case.max_functions),
        cached_case,
        commands,
    )
    target_jobs = min(max(1, jobs), len(selected)) if selected else 1
    # Target workers overlap function-level work, while the shared LimitedRunner
    # enforces the global subprocess cap. Let each target overlap its own command
    # probes too, otherwise one timeout-prone target can serialize several 180s
    # waits and dominate the whole benchmark.
    command_jobs = max(1, jobs)

    if not isolate_commands:
        targets = []
        case_events = []
        for chunk_idx, target_chunk in enumerate(target_batches(selected, batch_target_size)):
            chunk_tmpdir = (
                task_tmpdir.joinpath(f"batch-{chunk_idx}") if task_tmpdir is not None else None
            )
            chunk_targets, chunk_events = collect_targets_batched_adaptive(
                r2,
                case,
                target_chunk,
                timeout_s,
                repeat,
                include_sensitive,
                env,
                chunk_tmpdir,
                command_jobs,
                runner,
                commands,
                gold_manifest,
            )
            targets.extend(chunk_targets)
            for event in chunk_events:
                event["batch_index"] = chunk_idx
            case_events.extend(chunk_events)
        case_out["case_events"] = case_events
        case_out["targets"] = targets
        case_out["elapsed_s"] = round(time.perf_counter() - started, 6)
        case_out["failures"] = collect_failures(case_out)
        case_out["incomplete"] = case_result_has_incomplete_work(case_out, command_names)
        case_out["score"] = score_case(case_out)
        return case_out

    def collect_selected_target(target: dict[str, Any]) -> dict[str, Any]:
        return collect_target(
            r2,
            case,
            target,
            timeout_s,
            repeat,
            include_sensitive,
            env,
            task_tmpdir,
            command_jobs,
            runner,
            commands,
            gold_manifest,
        )

    case_out["targets"] = run_ordered_parallel(selected, target_jobs, collect_selected_target)
    case_out["elapsed_s"] = round(time.perf_counter() - started, 6)
    case_out["failures"] = collect_failures(case_out)
    case_out["incomplete"] = case_result_has_incomplete_work(case_out, command_names)
    case_out["score"] = score_case(case_out)
    return case_out


def aggregate(cases: list[dict[str, Any]]) -> dict[str, Any]:
    failures_by_kind: dict[str, int] = {}
    slow_commands: list[dict[str, Any]] = []
    runtime_buckets: dict[str, int] = {}
    decompile_quality_buckets: dict[str, int] = {}
    decompile_by_family: dict[str, dict[str, int]] = {}
    fallback_by_family: dict[str, int] = {}
    hard_failure_by_family: dict[str, int] = {}
    quality_gate_failures: dict[str, int] = {}
    gold_oracle_totals = {
        "expectations": 0,
        "commands": 0,
        "passed": 0,
        "failed": 0,
        "failures": 0,
    }
    owner_buckets: dict[str, int] = {}
    generic_arg_total = 0
    generic_type_total = 0
    decompile_metric_totals = {
        "argn_leak_total": 0,
        "comment_only_decompile_total": 0,
        "empty_loop_body_total": 0,
        "fake_while_break_wrapper_total": 0,
        "missing_return_nonvoid_total": 0,
        "raw_temp_stack_leak_total": 0,
        "summary_pseudo_call_total": 0,
        "undefined_identifier_return_total": 0,
        "unresolved_fcn_total": 0,
    }
    radare2_candidates = 0
    total_targets = 0
    pdg_comparisons: list[dict[str, Any]] = []
    target_rollups: list[dict[str, Any]] = []
    case_setup_elapsed_s = 0.0
    target_setup_elapsed_s = 0.0
    command_elapsed_s = 0.0
    engine_cache_totals: dict[str, dict[str, int]] = {}
    cache_totals: dict[str, dict[str, int]] = {}
    fast_path_totals = fast_path_totals_template()
    for case in cases:
        for event in case.get("case_events", []):
            if isinstance(event, dict):
                if event.get("command") == "case_setup":
                    case_setup_elapsed_s += _float_value(event.get("elapsed_s"))
                slow_commands.append(
                    {
                        "case": case.get("name"),
                        "corpus": case.get("corpus"),
                        "target": event.get("target"),
                        "command": event.get("command"),
                        "elapsed_s": event.get("elapsed_s", 0),
                    }
                )
        for failure in case.get("failures", []):
            kind = str(failure.get("kind", "unknown"))
            failures_by_kind[kind] = failures_by_kind.get(kind, 0) + 1
            owner = str(failure.get("owner") or owner_for_failure(kind, failure.get("command")))
            owner_buckets[owner] = owner_buckets.get(owner, 0) + 1
            family = target_family(failure.get("target"))
            hard_failure_by_family[family] = hard_failure_by_family.get(family, 0) + 1
            if kind == "radare2_candidate":
                radare2_candidates += 1
            if kind in QUALITY_GATE_FAILURES:
                quality_gate_failures[kind] = quality_gate_failures.get(kind, 0) + 1
        for native_key in ("native_discovery", "native_pdfj_probe"):
            native_result = case.get(native_key)
            if isinstance(native_result, dict):
                bucket = str(native_result.get("runtime_bucket") or "unknown")
                runtime_buckets[bucket] = runtime_buckets.get(bucket, 0) + 1
        for target in case.get("targets", []):
            if target.get("found", True):
                total_targets += 1
            target_name = target.get("name") or target.get("requested")
            target_keys = {
                str(value)
                for value in (target.get("name"), target.get("requested"))
                if value not in (None, "")
            }
            target_failures = [
                failure
                for failure in case.get("failures", [])
                if str(failure.get("target") or "") in target_keys
            ]
            target_elapsed_s = 0.0
            target_residual_count = 0
            target_generic_arg_count = 0
            target_generic_type_count = 0
            target_owner_buckets: dict[str, int] = {}
            for failure in target_failures:
                owner = str(
                    failure.get("owner")
                    or owner_for_failure(failure.get("kind"), failure.get("command"))
                )
                target_owner_buckets[owner] = target_owner_buckets.get(owner, 0) + 1
            comparison = pdg_target_comparison(case, target)
            if comparison is not None:
                pdg_comparisons.append(comparison)
            setup_event = target.get("setup_event")
            if isinstance(setup_event, dict):
                target_setup_elapsed_s += _float_value(setup_event.get("elapsed_s"))
                slow_commands.append(
                    {
                        "case": case.get("name"),
                        "corpus": case.get("corpus"),
                        "target": target.get("name") or target.get("requested"),
                        "command": "setup",
                        "elapsed_s": setup_event.get("elapsed_s", 0),
                    }
                )
            for command, result in target.get("commands", {}).items():
                elapsed_s = _float_value(result.get("elapsed_s"))
                command_elapsed_s += elapsed_s
                target_elapsed_s += elapsed_s
                bucket = str(result.get("runtime_bucket") or "unknown")
                runtime_buckets[bucket] = runtime_buckets.get(bucket, 0) + 1
                quality = result.get("decompile_quality")
                if isinstance(quality, dict):
                    decompile_metric_totals["argn_leak_total"] += int(
                        quality.get("argn_leak_count") or 0
                    )
                    decompile_metric_totals["comment_only_decompile_total"] += (
                        1 if quality.get("comment_only") else 0
                    )
                    decompile_metric_totals["fake_while_break_wrapper_total"] += int(
                        quality.get("fake_while_break_wrapper_count") or 0
                    )
                    decompile_metric_totals["empty_loop_body_total"] += int(
                        quality.get("empty_loop_body_count") or 0
                    )
                    decompile_metric_totals["missing_return_nonvoid_total"] += (
                        1 if quality.get("missing_return_nonvoid") else 0
                    )
                    decompile_metric_totals["raw_temp_stack_leak_total"] += int(
                        quality.get("raw_temp_stack_leak_count") or 0
                    )
                    decompile_metric_totals["summary_pseudo_call_total"] += int(
                        quality.get("summary_pseudo_call_count") or 0
                    )
                    decompile_metric_totals["undefined_identifier_return_total"] += int(
                        quality.get("undefined_identifier_return_count") or 0
                    )
                    decompile_metric_totals["unresolved_fcn_total"] += int(
                        quality.get("unresolved_fcn_count") or 0
                    )
                    classification = str(quality.get("classification") or "unknown")
                    decompile_quality_buckets[classification] = (
                        decompile_quality_buckets.get(classification, 0) + 1
                    )
                    if command.startswith("decompile"):
                        family = target_family(target.get("name") or target.get("requested"))
                        family_buckets = decompile_by_family.setdefault(family, {})
                        family_buckets[classification] = (
                            family_buckets.get(classification, 0) + 1
                        )
                        if classification == "fallback":
                            fallback_by_family[family] = fallback_by_family.get(family, 0) + 1
                        if classification == "residual":
                            target_residual_count += 1
                            owner_buckets["r2sym"] = owner_buckets.get("r2sym", 0) + 1
                            target_owner_buckets["r2sym"] = (
                                target_owner_buckets.get("r2sym", 0) + 1
                            )
                type_metrics = result.get("type_metrics")
                if isinstance(type_metrics, dict):
                    generic_arg_count = int(type_metrics.get("generic_arg_count") or 0)
                    generic_type_count = int(type_metrics.get("generic_type_count") or 0)
                    generic_arg_total += generic_arg_count
                    generic_type_total += generic_type_count
                    target_generic_arg_count += generic_arg_count
                    target_generic_type_count += generic_type_count
                    generic_total = generic_arg_count + generic_type_count
                    if generic_total:
                        owner_buckets["r2types"] = owner_buckets.get("r2types", 0) + generic_total
                        target_owner_buckets["r2types"] = (
                            target_owner_buckets.get("r2types", 0) + generic_total
                        )
                profile_metrics = result.get("profile_metrics")
                cache_metrics = result.get("cache_metrics")
                if isinstance(cache_metrics, dict):
                    add_cache_metrics_totals(engine_cache_totals, cache_totals, cache_metrics)
                elif isinstance(profile_metrics, dict):
                    decompile_cache = profile_metrics.get("decompile_cache")
                    if isinstance(decompile_cache, dict):
                        add_cache_counter_totals(
                            cache_totals.setdefault("decompile", {}),
                            decompile_cache,
                        )
                    engine_cache = profile_metrics.get("engine_cache")
                    if isinstance(engine_cache, dict):
                        add_engine_cache_totals(engine_cache_totals, engine_cache)
                fast_path_metrics = result.get("fast_path_metrics")
                if isinstance(fast_path_metrics, dict):
                    add_fast_path_totals(fast_path_totals, fast_path_metrics)
                gold_oracle = result.get("gold_oracle")
                if isinstance(gold_oracle, dict):
                    gold_oracle_totals["commands"] += 1
                    gold_oracle_totals["expectations"] += int(
                        gold_oracle.get("expectation_count") or 0
                    )
                    failure_count = len(
                        [
                            failure
                            for failure in gold_oracle.get("failures", [])
                            if isinstance(failure, dict)
                        ]
                    )
                    gold_oracle_totals["failures"] += failure_count
                    if failure_count:
                        gold_oracle_totals["failed"] += 1
                    else:
                        gold_oracle_totals["passed"] += 1
                slow_commands.append(
                    {
                        "case": case.get("name"),
                        "corpus": case.get("corpus"),
                        "target": target.get("name") or target.get("requested"),
                        "command": command,
                        "elapsed_s": result.get("elapsed_s", 0),
                    }
                )
            hard_failure_count = len(target_failures)
            if (
                hard_failure_count
                or target_residual_count
                or target_generic_arg_count
                or target_generic_type_count
                or target_elapsed_s >= 1.0
            ):
                target_rollups.append(
                    {
                        "case": case.get("name"),
                        "corpus": case.get("corpus"),
                        "target": target_name,
                        "family": target_family(target_name),
                        "hard_failures": hard_failure_count,
                        "residual_commands": target_residual_count,
                        "generic_arg_count": target_generic_arg_count,
                        "generic_type_count": target_generic_type_count,
                        "elapsed_s": round(target_elapsed_s, 6),
                        "failure_kinds": sorted(
                            {str(failure.get("kind") or "unknown") for failure in target_failures}
                        ),
                        "owner_buckets": dict(sorted(target_owner_buckets.items())),
                    }
                )
    slow_commands.sort(
        key=lambda item: (
            -float(item["elapsed_s"]),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
            str(item.get("command") or ""),
        )
    )
    target_rollups.sort(
        key=lambda item: (
            -int(item.get("hard_failures") or 0),
            -int(item.get("residual_commands") or 0),
            -int(item.get("generic_arg_count") or 0),
            -int(item.get("generic_type_count") or 0),
            -float(item.get("elapsed_s") or 0),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
        )
    )
    scores = [int(case.get("score", 0)) for case in cases]
    failures_sorted = dict(sorted(failures_by_kind.items()))
    setup_elapsed_s = case_setup_elapsed_s + target_setup_elapsed_s
    timing = {
        "case_setup_s": round(case_setup_elapsed_s, 6),
        "target_setup_s": round(target_setup_elapsed_s, 6),
        "setup_s": round(setup_elapsed_s, 6),
        "command_s": round(command_elapsed_s, 6),
        "setup_to_command_ratio": round(setup_elapsed_s / command_elapsed_s, 6)
        if command_elapsed_s > 0
        else None,
    }
    sorted_owner_buckets = dict(sorted(owner_buckets.items()))
    pdg_summary = summarize_pdg_comparisons(pdg_comparisons)
    return {
        "case_count": len(cases),
        "target_count": total_targets,
        "average_score": round(sum(scores) / len(scores), 2) if scores else 0.0,
        "min_score": min(scores) if scores else 0,
        "failures_by_kind": failures_sorted,
        "timing": timing,
        "cache": {
            "engine": {
                key: dict(sorted(value.items()))
                for key, value in sorted(engine_cache_totals.items())
            },
            **{
                key: dict(sorted(value.items()))
                for key, value in sorted(cache_totals.items())
            },
        },
        "fast_paths": finalized_fast_path_totals(fast_path_totals),
        "quality": {
            "decompile": dict(sorted(decompile_quality_buckets.items())),
            "decompile_by_family": {
                family: dict(sorted(buckets.items()))
                for family, buckets in sorted(decompile_by_family.items())
            },
            "fallback_by_family": dict(sorted(fallback_by_family.items())),
            "hard_failure_by_family": dict(sorted(hard_failure_by_family.items())),
            "owner_buckets": sorted_owner_buckets,
            "runtime_buckets": dict(sorted(runtime_buckets.items())),
            "manual_gate_failures": dict(sorted(quality_gate_failures.items())),
            "gold_oracle": dict(sorted(gold_oracle_totals.items())),
            **decompile_metric_totals,
            "generic_arg_total": generic_arg_total,
            "generic_type_total": generic_type_total,
            "radare2_candidate_count": radare2_candidates,
            "pdg_comparison": pdg_summary,
        },
        "next_work": benchmark_next_work(
            sorted_owner_buckets,
            target_rollups,
            slow_commands,
            timing,
            pdg_summary,
        ),
        "slowest_commands": slow_commands[:20],
        "worst_targets": target_rollups[:20],
    }


def collect_command_events(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for case in cases:
        case_events = case.get("case_events")
        if isinstance(case_events, list):
            events.extend(event for event in case_events if isinstance(event, dict))
        for target in case.get("targets", []):
            target_events = target.get("command_events")
            if isinstance(target_events, list):
                events.extend(event for event in target_events if isinstance(event, dict))
    events.sort(
        key=lambda item: (
            float(item.get("started_at") or 0.0),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
            str(item.get("command") or ""),
            int(item.get("repeat_idx") or 0),
        )
    )
    return events


def load_report(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text())
    if not isinstance(payload, dict):
        raise ValueError(f"{path} is not a benchmark report object")
    return payload


def _summary_metric(report: dict[str, Any], path: tuple[str, ...], default: Any = 0) -> Any:
    current: Any = report
    for part in path:
        if not isinstance(current, dict):
            return default
        current = current.get(part)
    return default if current is None else current


def _hard_failure_count(report: dict[str, Any]) -> int:
    failures = _summary_metric(report, ("summary", "failures_by_kind"), {})
    if not isinstance(failures, dict):
        return 0
    hard_kinds = {
        "command_return",
        "decompiler_fallback",
        "discovery_parse",
        "discovery_return",
        "empty_decompile",
        "json_parse",
        "missing_target",
        "radare2_candidate",
        "timeout",
        "zero_functions",
        GOLD_ORACLE_FAILURE,
        *QUALITY_GATE_FAILURES,
    }
    return sum(int(failures.get(kind) or 0) for kind in hard_kinds)


def owner_for_failure(kind: Any, command: Any = None) -> str:
    failure_kind = str(kind or "unknown")
    owner = FAILURE_OWNER.get(failure_kind)
    if owner:
        return owner
    command_name = str(command or "")
    if command_name == "types":
        return "r2types"
    if command_name.startswith(DECOMPILE_COMMAND_PREFIX):
        return "r2dec"
    if command_name == "profile":
        return "r2engine"
    return "unknown"


def strict_quality_gate(args: argparse.Namespace, report: dict[str, Any]) -> dict[str, Any]:
    checks = {
        "hard_failures": {
            "value": _hard_failure_count(report),
            "max": getattr(args, "max_hard_failures", None),
        },
        "residual_decompile": {
            "value": int(_summary_metric(report, ("summary", "quality", "decompile", "residual"), 0) or 0),
            "max": getattr(args, "max_residual_decompile", None),
        },
        "generic_args": {
            "value": int(_summary_metric(report, ("summary", "quality", "generic_arg_total"), 0) or 0),
            "max": getattr(args, "max_generic_args", None),
        },
        "generic_types": {
            "value": int(_summary_metric(report, ("summary", "quality", "generic_type_total"), 0) or 0),
            "max": getattr(args, "max_generic_types", None),
        },
        "average_score": {
            "value": float(_summary_metric(report, ("summary", "average_score"), 0.0) or 0.0),
            "min": getattr(args, "min_average_score", None),
        },
        "setup_command_ratio": {
            "value": _summary_metric(report, ("summary", "timing", "setup_to_command_ratio"), None),
            "max": getattr(args, "max_setup_command_ratio", None),
        },
        "pdg_quality_wins": {
            "value": int(
                _summary_metric(
                    report,
                    ("summary", "quality", "pdg_comparison", "quality", "pdg"),
                    0,
                )
                or 0
            ),
            "max": getattr(args, "max_pdg_quality_wins", None),
        },
        "pdg_perf_wins": {
            "value": int(
                _summary_metric(
                    report,
                    ("summary", "quality", "pdg_comparison", "perf", "pdg"),
                    0,
                )
                or 0
            ),
            "max": getattr(args, "max_pdg_perf_wins", None),
        },
        "pdg_quality_then_perf_wins": {
            "value": int(
                _summary_metric(
                    report,
                    (
                        "summary",
                        "quality",
                        "pdg_comparison",
                        "quality_then_perf",
                        "pdg",
                    ),
                    0,
                )
                or 0
            ),
            "max": getattr(args, "max_pdg_quality_then_perf_wins", None),
        },
        "pdg_successful_common_targets": {
            "value": int(
                _summary_metric(
                    report,
                    ("summary", "quality", "pdg_comparison", "successful_common_targets"),
                    0,
                )
                or 0
            ),
            "min": 1 if getattr(args, "require_pdg_comparison", False) else None,
        },
        "gold_failures": {
            "value": int(
                _summary_metric(
                    report,
                    ("summary", "quality", "gold_oracle", "failures"),
                    0,
                )
                or 0
            ),
            "max": getattr(args, "max_gold_failures", None),
        },
        "gold_expectations": {
            "value": int(
                _summary_metric(
                    report,
                    ("summary", "quality", "gold_oracle", "expectations"),
                    0,
                )
                or 0
            ),
            "min": 1 if getattr(args, "require_gold", False) else None,
        },
    }
    failures: list[dict[str, Any]] = []
    for metric, check in checks.items():
        value = check["value"]
        maximum = check.get("max")
        minimum = check.get("min")
        if value is None:
            continue
        if maximum is not None and value > maximum:
            failures.append(
                {
                    "metric": metric,
                    "value": value,
                    "limit": maximum,
                    "op": "<=",
                }
            )
        if minimum is not None and value < minimum:
            failures.append(
                {
                    "metric": metric,
                    "value": value,
                    "limit": minimum,
                    "op": ">=",
                }
            )
    return {
        "status": "ok" if not failures else "failed",
        "checks": checks,
        "failures": failures,
    }


def _metric_delta(before: Any, after: Any) -> dict[str, Any]:
    try:
        delta = round(float(after) - float(before), 6)
    except (TypeError, ValueError):
        delta = None
    return {"before": before, "after": after, "delta": delta}


def _slowest_by_key(report: dict[str, Any]) -> dict[tuple[str, str, str, str], float]:
    slowest = _summary_metric(report, ("summary", "slowest_commands"), [])
    out: dict[tuple[str, str, str, str], float] = {}
    if not isinstance(slowest, list):
        return out
    for item in slowest:
        if not isinstance(item, dict):
            continue
        key = (
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
            str(item.get("command") or ""),
        )
        out[key] = float(item.get("elapsed_s") or 0.0)
    return out


def compare_reports(before: dict[str, Any], after: dict[str, Any]) -> dict[str, Any]:
    before_slowest = _slowest_by_key(before)
    after_slowest = _slowest_by_key(after)
    slow_delta = []
    for key in sorted(set(before_slowest) | set(after_slowest)):
        before_elapsed = before_slowest.get(key, 0.0)
        after_elapsed = after_slowest.get(key, 0.0)
        corpus, case, target, command = key
        slow_delta.append(
            {
                "corpus": corpus,
                "case": case,
                "target": target,
                "command": command,
                "before_s": round(before_elapsed, 6),
                "after_s": round(after_elapsed, 6),
                "delta_s": round(after_elapsed - before_elapsed, 6),
            }
        )
    slow_delta.sort(
        key=lambda item: (
            -abs(float(item["delta_s"])),
            str(item.get("corpus") or ""),
            str(item.get("case") or ""),
            str(item.get("target") or ""),
            str(item.get("command") or ""),
        )
    )

    metrics = {
        "status": {"before": before.get("status"), "after": after.get("status")},
        "next_work_status": {
            "before": _summary_metric(before, ("summary", "next_work", "status"), None),
            "after": _summary_metric(after, ("summary", "next_work", "status"), None),
        },
        "elapsed_s": _metric_delta(before.get("elapsed_s"), after.get("elapsed_s")),
        "setup_s": _metric_delta(
            _summary_metric(before, ("summary", "timing", "setup_s")),
            _summary_metric(after, ("summary", "timing", "setup_s")),
        ),
        "setup_command_ratio": _metric_delta(
            _summary_metric(before, ("summary", "timing", "setup_to_command_ratio")),
            _summary_metric(after, ("summary", "timing", "setup_to_command_ratio")),
        ),
        "command_s": _metric_delta(
            _summary_metric(before, ("summary", "timing", "command_s")),
            _summary_metric(after, ("summary", "timing", "command_s")),
        ),
        "engine_cache_total_hits": _metric_delta(
            _summary_metric(before, ("summary", "cache", "engine", "total", "hits")),
            _summary_metric(after, ("summary", "cache", "engine", "total", "hits")),
        ),
        "engine_cache_total_misses": _metric_delta(
            _summary_metric(before, ("summary", "cache", "engine", "total", "misses")),
            _summary_metric(after, ("summary", "cache", "engine", "total", "misses")),
        ),
        "decompile_cache_hits": _metric_delta(
            _summary_metric(before, ("summary", "cache", "decompile", "hits")),
            _summary_metric(after, ("summary", "cache", "decompile", "hits")),
        ),
        "summary_cache_hits": _metric_delta(
            _summary_metric(before, ("summary", "cache", "summary", "hits")),
            _summary_metric(after, ("summary", "cache", "summary", "hits")),
        ),
        "summary_fast_path_count": _metric_delta(
            _summary_metric(before, ("summary", "fast_paths", "summary_fast_path_count")),
            _summary_metric(after, ("summary", "fast_paths", "summary_fast_path_count")),
        ),
        "average_score": _metric_delta(
            _summary_metric(before, ("summary", "average_score")),
            _summary_metric(after, ("summary", "average_score")),
        ),
        "min_score": _metric_delta(
            _summary_metric(before, ("summary", "min_score")),
            _summary_metric(after, ("summary", "min_score")),
        ),
        "hard_failures": _metric_delta(_hard_failure_count(before), _hard_failure_count(after)),
        "residual_decompile_count": _metric_delta(
            _summary_metric(before, ("summary", "quality", "decompile", "residual")),
            _summary_metric(after, ("summary", "quality", "decompile", "residual")),
        ),
        "generic_arg_total": _metric_delta(
            _summary_metric(before, ("summary", "quality", "generic_arg_total")),
            _summary_metric(after, ("summary", "quality", "generic_arg_total")),
        ),
        "generic_type_total": _metric_delta(
            _summary_metric(before, ("summary", "quality", "generic_type_total")),
            _summary_metric(after, ("summary", "quality", "generic_type_total")),
        ),
        "radare2_candidate_count": _metric_delta(
            _summary_metric(before, ("summary", "quality", "radare2_candidate_count")),
            _summary_metric(after, ("summary", "quality", "radare2_candidate_count")),
        ),
        "pdg_common_targets": _metric_delta(
            _summary_metric(before, ("summary", "quality", "pdg_comparison", "common_targets")),
            _summary_metric(after, ("summary", "quality", "pdg_comparison", "common_targets")),
        ),
        "pdg_successful_common_targets": _metric_delta(
            _summary_metric(
                before,
                ("summary", "quality", "pdg_comparison", "successful_common_targets"),
            ),
            _summary_metric(
                after,
                ("summary", "quality", "pdg_comparison", "successful_common_targets"),
            ),
        ),
        "sla_quality_wins_vs_pdg": _metric_delta(
            _summary_metric(before, ("summary", "quality", "pdg_comparison", "quality", "sla")),
            _summary_metric(after, ("summary", "quality", "pdg_comparison", "quality", "sla")),
        ),
        "pdg_quality_wins_vs_sla": _metric_delta(
            _summary_metric(before, ("summary", "quality", "pdg_comparison", "quality", "pdg")),
            _summary_metric(after, ("summary", "quality", "pdg_comparison", "quality", "pdg")),
        ),
        "sla_perf_wins_vs_pdg": _metric_delta(
            _summary_metric(before, ("summary", "quality", "pdg_comparison", "perf", "sla")),
            _summary_metric(after, ("summary", "quality", "pdg_comparison", "perf", "sla")),
        ),
        "pdg_perf_wins_vs_sla": _metric_delta(
            _summary_metric(before, ("summary", "quality", "pdg_comparison", "perf", "pdg")),
            _summary_metric(after, ("summary", "quality", "pdg_comparison", "perf", "pdg")),
        ),
        "sla_quality_then_perf_wins_vs_pdg": _metric_delta(
            _summary_metric(
                before,
                ("summary", "quality", "pdg_comparison", "quality_then_perf", "sla"),
            ),
            _summary_metric(
                after,
                ("summary", "quality", "pdg_comparison", "quality_then_perf", "sla"),
            ),
        ),
        "pdg_quality_then_perf_wins_vs_sla": _metric_delta(
            _summary_metric(
                before,
                ("summary", "quality", "pdg_comparison", "quality_then_perf", "pdg"),
            ),
            _summary_metric(
                after,
                ("summary", "quality", "pdg_comparison", "quality_then_perf", "pdg"),
            ),
        ),
    }
    return {
        "schema": SCHEMA_VERSION,
        "metrics": metrics,
        "failures_by_kind": {
            "before": _summary_metric(before, ("summary", "failures_by_kind"), {}),
            "after": _summary_metric(after, ("summary", "failures_by_kind"), {}),
        },
        "owner_buckets": {
            "before": _summary_metric(before, ("summary", "quality", "owner_buckets"), {}),
            "after": _summary_metric(after, ("summary", "quality", "owner_buckets"), {}),
        },
        "next_work": {
            "before": _summary_metric(before, ("summary", "next_work"), {}),
            "after": _summary_metric(after, ("summary", "next_work"), {}),
        },
        "slowest_command_delta": slow_delta[:20],
    }


def write_report(path: Path, report: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    tmp_path = path.with_name(f".{path.name}.tmp")
    tmp_path.write_text(payload)
    tmp_path.replace(path)


def stable_json_hash(payload: Any) -> str:
    data = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def plugin_fingerprint(plugin_dir: str) -> dict[str, Any]:
    if not plugin_dir:
        return {"kind": "none", "hash": "none", "files": []}
    root = Path(plugin_dir)
    if not root.exists():
        return {"kind": "missing", "hash": stable_json_hash(str(root)), "files": []}
    suffixes = {".so", ".dylib", ".dll"}
    if root.is_file():
        candidates = [root]
    else:
        candidates = [
            path
            for path in root.rglob("*")
            if path.is_file()
            and (path.suffix.lower() in suffixes or path.name.startswith("anal_sleigh."))
        ]
    entries: list[dict[str, Any]] = []
    for path in sorted(candidates, key=lambda item: str(item.relative_to(root)) if root.is_dir() else str(item)):
        try:
            stat_result = path.stat()
        except OSError:
            continue
        rel = str(path.relative_to(root)) if root.is_dir() else path.name
        entries.append(
            {
                "path": rel,
                "size": stat_result.st_size,
                "sha256": file_sha256(path),
            }
        )
    return {
        "kind": "artifacts" if entries else "empty",
        "hash": stable_json_hash(entries),
        "files": entries,
    }


def benchmark_execution_config(
    args: argparse.Namespace,
    plugin_info: dict[str, Any],
    *,
    total_jobs: int,
    case_jobs: int,
    command_jobs: int,
) -> dict[str, Any]:
    execution_mode = "isolated" if args.isolate_commands else "batched"
    config = {
        "schema": SCHEMA_VERSION,
        "r2": args.r2,
        "plugin_hash": plugin_info.get("hash"),
        "analysis": args.analysis,
        "repeat": max(1, args.repeat),
        "cache_probe": bool(getattr(args, "cache_probe", False)),
        "closure_gate": bool(getattr(args, "closure_gate", False)),
        "timeout": args.timeout,
        "execution_mode": execution_mode,
        "batch_target_size": args.batch_target_size,
        "jobs": total_jobs,
        "case_workers": case_jobs,
        "per_case_workers": command_jobs,
        "include_sensitive": bool(args.include_sensitive),
        "manifest": args.manifest or "",
        "gold_manifest": getattr(args, "gold_manifest", "") or "",
        "gold_manifest_hash": gold_manifest_hash(getattr(args, "gold_manifest", "")),
        "manifest_only": bool(args.manifest_only),
        "override_manifest_max_functions": bool(
            getattr(args, "override_manifest_max_functions", False)
        ),
        "focused_coreutils": bool(args.focused_coreutils),
        "no_repo_fixtures": bool(args.no_repo_fixtures),
        "max_binaries_per_corpus": args.max_binaries_per_corpus,
        "global_targets": list(args.target),
        "commands": list(parse_command_filter(args.commands)),
        "baseline_plugin_dirs": list(args.baseline_plugin_dir or []),
        "strict_thresholds": {
            "max_hard_failures": getattr(args, "max_hard_failures", None),
            "max_residual_decompile": getattr(args, "max_residual_decompile", None),
            "max_generic_args": getattr(args, "max_generic_args", None),
            "max_generic_types": getattr(args, "max_generic_types", None),
            "min_average_score": getattr(args, "min_average_score", None),
            "max_setup_command_ratio": getattr(args, "max_setup_command_ratio", None),
            "require_pdg_comparison": bool(getattr(args, "require_pdg_comparison", False)),
            "max_pdg_quality_wins": getattr(args, "max_pdg_quality_wins", None),
            "max_pdg_perf_wins": getattr(args, "max_pdg_perf_wins", None),
            "max_pdg_quality_then_perf_wins": getattr(
                args,
                "max_pdg_quality_then_perf_wins",
                None,
            ),
            "max_gold_failures": getattr(args, "max_gold_failures", None),
            "require_gold": bool(getattr(args, "require_gold", False)),
        },
    }
    config["run_config_hash"] = stable_json_hash(config)
    return config


def case_descriptor(case: BinaryCase) -> dict[str, Any]:
    try:
        stat_result = case.path.stat()
        size = stat_result.st_size
        mtime_ns = stat_result.st_mtime_ns
    except OSError:
        size = None
        mtime_ns = None
    return {
        "name": case.name,
        "corpus": case.corpus,
        "path": str(case.path.resolve()),
        "size": size,
        "mtime_ns": mtime_ns,
        "analysis": case.analysis,
        "targets": list(case.targets),
        "max_functions": case.max_functions,
    }


def case_cache_key(case: BinaryCase, run_config_hash: str) -> str:
    return stable_json_hash(
        {
            "run_config_hash": run_config_hash,
            "case": case_descriptor(case),
        }
    )


def load_resume_cases(path: Path, run_config_hash: str) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    try:
        report = load_report(path)
    except (OSError, ValueError, json.JSONDecodeError):
        return {}
    config = report.get("benchmark_config")
    if not isinstance(config, dict) or config.get("run_config_hash") != run_config_hash:
        return {}
    out: dict[str, dict[str, Any]] = {}
    for case in report.get("cases", []):
        if not isinstance(case, dict):
            continue
        key = case.get("benchmark_case_key")
        if isinstance(key, str) and key:
            out[key] = case
    return out


def case_result_has_incomplete_work(
    case_result: dict[str, Any],
    command_names: tuple[str, ...] | None = None,
) -> bool:
    expected = set(command_names or tuple(TARGET_COMMAND_DEFS))
    for target in case_result.get("targets", []):
        if not isinstance(target, dict) or not target.get("found", True):
            continue
        commands = target.get("commands")
        if not isinstance(commands, dict):
            return True
        if expected and any(name not in commands for name in expected):
            return True
        for name in expected or set(commands):
            entry = commands.get(name)
            if not isinstance(entry, dict):
                return True
            if entry.get("skipped") is True or section_status_incomplete(entry.get("section_status")):
                return True
    return False


def worst_targets(cases: list[dict[str, Any]]) -> dict[str, Any]:
    timeouts: list[dict[str, Any]] = []
    not_reached: list[dict[str, Any]] = []
    fallbacks: list[dict[str, Any]] = []
    generic_types: list[dict[str, Any]] = []
    retry_attribution: dict[str, int] = {}
    for case in cases:
        for target in case.get("targets", []):
            target_name = target.get("name") or target.get("requested")
            mode = target.get("attribution_mode")
            if isinstance(mode, str):
                retry_attribution[mode] = retry_attribution.get(mode, 0) + 1
            for command, result in target.get("commands", {}).items():
                if not isinstance(result, dict):
                    continue
                result_mode = result.get("attribution_mode")
                if isinstance(result_mode, str):
                    key = f"command:{result_mode}"
                    retry_attribution[key] = retry_attribution.get(key, 0) + 1
                section_status = result.get("section_status")
                if result.get("skipped") is True or section_status in INCOMPLETE_SECTION_STATUSES:
                    not_reached.append(
                        {
                            "case": case.get("name"),
                            "corpus": case.get("corpus"),
                            "target": target_name,
                            "command": command,
                            "section_status": section_status or BATCH_SECTION_NOT_REACHED,
                            "attribution_mode": result.get("attribution_mode"),
                            "retry_origin": result.get("retry_origin"),
                        }
                    )
                    continue
                if result.get("timeout") or (
                    isinstance(result.get("event"), dict) and result["event"].get("timeout")
                ):
                    timeouts.append(
                        {
                            "case": case.get("name"),
                            "corpus": case.get("corpus"),
                            "target": target_name,
                            "command": command,
                            "elapsed_s": result.get("elapsed_s", 0),
                            "attribution_mode": result.get("attribution_mode"),
                            "retry_origin": result.get("retry_origin"),
                        }
                    )
                quality = result.get("decompile_quality")
                if isinstance(quality, dict) and quality.get("classification") == "fallback":
                    fallbacks.append(
                        {
                            "case": case.get("name"),
                            "corpus": case.get("corpus"),
                            "target": target_name,
                            "family": target_family(target_name),
                            "command": command,
                            "elapsed_s": result.get("elapsed_s", 0),
                        }
                    )
                type_metrics = result.get("type_metrics")
                if isinstance(type_metrics, dict):
                    generic_count = int(type_metrics.get("generic_arg_count") or 0) + int(
                        type_metrics.get("generic_type_count") or 0
                    )
                    if generic_count:
                        generic_types.append(
                            {
                                "case": case.get("name"),
                                "corpus": case.get("corpus"),
                                "target": target_name,
                                "generic_count": generic_count,
                                "generic_args": int(type_metrics.get("generic_arg_count") or 0),
                                "generic_types": int(type_metrics.get("generic_type_count") or 0),
                                "ret_type": type_metrics.get("ret_type"),
                            }
                        )
    timeouts.sort(key=lambda item: (-float(item.get("elapsed_s") or 0), str(item.get("case") or ""), str(item.get("target") or "")))
    not_reached.sort(key=lambda item: (str(item.get("case") or ""), str(item.get("target") or ""), str(item.get("command") or "")))
    fallbacks.sort(key=lambda item: (str(item.get("family") or ""), str(item.get("case") or ""), str(item.get("target") or ""), str(item.get("command") or "")))
    generic_types.sort(key=lambda item: (-int(item.get("generic_count") or 0), str(item.get("case") or ""), str(item.get("target") or "")))
    return {
        "timeouts": timeouts[:20],
        "not_reached": not_reached[:40],
        "fallbacks": fallbacks[:40],
        "generic_type_targets": generic_types[:20],
        "retry_attribution": dict(sorted(retry_attribution.items())),
    }


def build_benchmark_report(
    args: argparse.Namespace,
    results: list[dict[str, Any]],
    *,
    elapsed_s: float,
    total_jobs: int,
    case_jobs: int,
    command_jobs: int,
    total_cases: int,
    resumed_cases: int,
    plugin_info: dict[str, Any],
    benchmark_config: dict[str, Any],
    command_names: tuple[str, ...],
) -> dict[str, Any]:
    incomplete_cases = [
        result.get("name")
        for result in results
        if case_result_has_incomplete_work(result, command_names)
    ]
    complete = len(results) == total_cases and not incomplete_cases
    status = "running"
    if len(results) == total_cases and incomplete_cases:
        status = "incomplete"
    elif complete:
        status = "ok" if all(not result.get("failures") for result in results) else "issues"
    report = {
        "schema": SCHEMA_VERSION,
        "status": status,
        "elapsed_s": round(elapsed_s, 6),
        "r2": args.r2,
        "analysis": args.analysis,
        "repeat": max(1, args.repeat),
        "execution_mode": "isolated" if args.isolate_commands else "batched",
        "commands": list(command_names),
        "parallelism": {
            "jobs": total_jobs,
            "case_workers": case_jobs,
            "per_case_workers": command_jobs,
            "batch_target_size": args.batch_target_size,
        },
        "inputs": {
            "manifest": args.manifest or None,
            "gold_manifest": getattr(args, "gold_manifest", "") or None,
            "manifest_only": bool(args.manifest_only),
            "repo_fixtures": not args.no_repo_fixtures,
            "coreutils_dir": display_path(Path(args.coreutils_dir), args.include_sensitive) if args.coreutils_dir else None,
            "cgc_dir": display_path(Path(args.cgc_dir), args.include_sensitive) if args.cgc_dir else None,
            "juliet_dir": display_path(Path(args.juliet_dir), args.include_sensitive) if args.juliet_dir else None,
            "kernel": display_path(Path(args.kernel), args.include_sensitive) if args.kernel else None,
            "preset": args.preset or None,
        },
        "checkpoint": {
            "enabled": bool(args.resume),
            "complete": complete,
            "completed_cases": len(results),
            "total_cases": total_cases,
            "resumed_cases": resumed_cases,
            "incomplete_cases": incomplete_cases,
        },
        "benchmark_config": {
            **benchmark_config,
            "plugin": plugin_info,
        },
        "events": collect_command_events(results),
        "summary": aggregate(results),
        "worst_targets": worst_targets(results),
        "cases": results,
    }
    if total_cases == 0:
        report["status"] = "skipped"
        report["reason"] = "no benchmark binaries found"
    return report


def run_cases_with_checkpoint(
    cases: list[BinaryCase],
    jobs: int,
    worker: Callable[[BinaryCase, dict[str, Any] | None], dict[str, Any]],
    *,
    case_keys: list[str],
    resume_cases: dict[str, dict[str, Any]],
    command_names: tuple[str, ...] | None = None,
    checkpoint: Callable[[list[dict[str, Any]], int], None],
) -> tuple[list[dict[str, Any]], int]:
    results: list[dict[str, Any] | None] = [None] * len(cases)
    resumed = 0
    pending: list[tuple[int, BinaryCase, dict[str, Any] | None]] = []
    for idx, case in enumerate(cases):
        cached = resume_cases.get(case_keys[idx])
        if cached is not None and not case_result_has_incomplete_work(cached, command_names):
            result = dict(cached)
            result["resumed_from_checkpoint"] = True
            result["benchmark_case_key"] = case_keys[idx]
            results[idx] = result
            resumed += 1
        else:
            pending.append((idx, case, cached))

    def completed_results() -> list[dict[str, Any]]:
        return [cast(dict[str, Any], result) for result in results if result is not None]

    if resumed:
        checkpoint(completed_results(), resumed)
    if not pending:
        return completed_results(), resumed

    def run_pending(item: tuple[int, BinaryCase, dict[str, Any] | None]) -> tuple[int, dict[str, Any]]:
        idx, case, cached = item
        result = worker(case, cached)
        result["benchmark_case_key"] = case_keys[idx]
        if cached is not None:
            result["resumed_partial_checkpoint"] = True
        return idx, result

    max_workers = min(max(1, jobs), len(pending))
    if max_workers <= 1:
        for item in pending:
            idx, result = run_pending(item)
            results[idx] = result
            checkpoint(completed_results(), resumed)
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {executor.submit(run_pending, item): item[0] for item in pending}
            for future in concurrent.futures.as_completed(futures):
                idx, result = future.result()
                results[idx] = result
                checkpoint(completed_results(), resumed)
    return completed_results(), resumed


def main() -> int:
    args = parse_args()
    if args.compare:
        before = load_report(Path(args.compare[0]))
        after = load_report(Path(args.compare[1]))
        print(json.dumps(compare_reports(before, after), indent=2, sort_keys=True))
        return 0
    benchmark_started = time.perf_counter()
    try:
        command_names = parse_command_filter(args.commands)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    try:
        gold_manifest = load_gold_manifest(args.gold_manifest)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"error: invalid gold manifest: {exc}", file=sys.stderr)
        return 2
    cases = build_cases(args)
    tmpdir = Path(args.tmpdir) if args.tmpdir else None
    env = build_r2_env(args.r2, args.plugin_dir, args.baseline_plugin_dir or [], tmpdir)
    total_jobs = max(1, int(args.jobs))
    case_jobs, command_jobs = parallel_split(total_jobs, len(cases))
    runner: Runner = LimitedRunner(run_r2, total_jobs) if total_jobs > 1 else run_r2
    plugin_info = plugin_fingerprint(args.plugin_dir)
    benchmark_config = benchmark_execution_config(
        args,
        plugin_info,
        total_jobs=total_jobs,
        case_jobs=case_jobs,
        command_jobs=command_jobs,
    )
    run_config_hash = str(benchmark_config["run_config_hash"])
    case_keys = [case_cache_key(case, run_config_hash) for case in cases]
    out_path = Path(args.out)
    resume_cases = load_resume_cases(out_path, run_config_hash) if args.resume else {}

    def run_selected_case(
        case: BinaryCase,
        cached_case: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        return run_case(
            args.r2,
            case,
            args.timeout,
            args.repeat,
            args.include_sensitive,
            env,
            tmpdir,
            command_jobs,
            runner,
            args.isolate_commands,
            args.batch_target_size,
            command_names,
            cached_case,
            gold_manifest,
        )

    def write_checkpoint(partial_results: list[dict[str, Any]], resumed_cases: int) -> None:
        report = build_benchmark_report(
            args,
            partial_results,
            elapsed_s=time.perf_counter() - benchmark_started,
            total_jobs=total_jobs,
            case_jobs=case_jobs,
            command_jobs=command_jobs,
            total_cases=len(cases),
            resumed_cases=resumed_cases,
            plugin_info=plugin_info,
            benchmark_config=benchmark_config,
            command_names=command_names,
        )
        write_report(out_path, report)

    results, resumed_count = run_cases_with_checkpoint(
        cases,
        case_jobs,
        run_selected_case,
        case_keys=case_keys,
        resume_cases=resume_cases,
        command_names=command_names,
        checkpoint=write_checkpoint if args.resume else lambda _results, _resumed: None,
    )
    elapsed_s = round(time.perf_counter() - benchmark_started, 6)
    report = build_benchmark_report(
        args,
        results,
        elapsed_s=elapsed_s,
        total_jobs=total_jobs,
        case_jobs=case_jobs,
        command_jobs=command_jobs,
        total_cases=len(cases),
        resumed_cases=resumed_count,
        plugin_info=plugin_info,
        benchmark_config=benchmark_config,
        command_names=command_names,
    )
    strict_gate = strict_quality_gate(args, report)
    report["strict_quality_gate"] = strict_gate
    write_report(out_path, report)
    print(
        "reversing benchmark "
        f"{report['status']}; cases={report['summary']['case_count']} "
        f"avg_score={report['summary']['average_score']} jobs={total_jobs} wrote {out_path}"
    )
    if args.strict and (report["status"] != "ok" or strict_gate["status"] != "ok"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
