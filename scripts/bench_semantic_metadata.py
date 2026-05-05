#!/usr/bin/env python3
"""Advisory benchmark for semantic metadata quality and aaaa overhead."""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_RUNS = 7
DEFAULT_MAX_OVERHEAD_PCT = 5.0
AFVJ_POINTER_FUNCS = (
    "dbg.safe_array_access",
    "dbg.test_array_index",
    "dbg.vuln_memcpy",
)


@dataclass
class CmdResult:
    returncode: int
    stdout: str
    stderr: str
    elapsed_s: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark semantic metadata output and advisory aaaa overhead."
    )
    parser.add_argument("--r2", default="r2", help="radare2 executable path")
    parser.add_argument(
        "--runs",
        type=int,
        default=DEFAULT_RUNS,
        help="number of repeated runs for timing medians (default: 7)",
    )
    parser.add_argument(
        "--max-overhead-pct",
        type=float,
        default=DEFAULT_MAX_OVERHEAD_PCT,
        help="advisory overhead threshold percentage (default: 5.0)",
    )
    parser.add_argument(
        "--json-out",
        default="",
        help="optional output path for machine-readable JSON report",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit non-zero when advisory thresholds fail",
    )
    return parser.parse_args()


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def vuln_test_path() -> Path:
    root = repo_root()
    primary = root / "tests" / "e2e" / "vuln_test"
    if primary.exists():
        return primary
    return Path("tests/e2e/vuln_test")


def run_r2(r2: str, binary: str, cmd: str, timeout_s: int = 240) -> CmdResult:
    argv = [r2, "-q", "-e", "bin.relocs.apply=true", "-c", cmd, binary]
    start = time.perf_counter()
    proc = subprocess.run(
        argv,
        capture_output=True,
        text=True,
        timeout=timeout_s,
        check=False,
    )
    elapsed = time.perf_counter() - start
    return CmdResult(
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
        elapsed_s=elapsed,
    )


def parse_json_payload(text: str) -> Any:
    stripped = text.strip()
    if not stripped:
        raise ValueError("empty output")

    # r2 occasionally emits non-JSON lines before the payload.
    for idx, ch in enumerate(stripped):
        if ch not in "[{":
            continue
        candidate = stripped[idx:]
        try:
            return json.loads(candidate)
        except json.JSONDecodeError:
            continue
    raise ValueError("no JSON payload found in output")


def count_semantic_lines(comments_payload: Any) -> dict[str, int]:
    semantic_lines = 0
    meta_lines = 0
    if not isinstance(comments_payload, list):
        return {"semantic_lines": 0, "meta_lines": 0}

    for entry in comments_payload:
        if not isinstance(entry, dict):
            continue
        comment = entry.get("name")
        if not isinstance(comment, str):
            continue
        for line in comment.splitlines():
            stripped = line.lstrip()
            if stripped.startswith("sla:"):
                semantic_lines += 1
                if "meta " in stripped:
                    meta_lines += 1
    return {"semantic_lines": semantic_lines, "meta_lines": meta_lines}


def collect_comment_metrics(
    r2: str, binary: str, metadata_enabled: bool, force_x86: bool
) -> dict[str, Any]:
    analysis_cmd = "aaaa" if metadata_enabled else "aa"
    cmd_parts = []
    if force_x86:
        cmd_parts.extend(["e anal.arch=x86", "e arch.bits=64"])
    cmd_parts.extend(
        [
            "a:sla.info >/dev/null",
            analysis_cmd,
            "CCj",
        ]
    )
    result = run_r2(r2, binary, "; ".join(cmd_parts))

    out: dict[str, Any] = {
        "returncode": result.returncode,
        "elapsed_s": round(result.elapsed_s, 6),
    }
    if result.returncode != 0 and result.stderr.strip():
        out["stderr"] = result.stderr.strip()
    try:
        payload = parse_json_payload(result.stdout)
        out.update(count_semantic_lines(payload))
    except Exception as exc:  # noqa: BLE001
        out["error"] = f"{exc}"
        out["semantic_lines"] = 0
        out["meta_lines"] = 0
    return out


def collect_afvj_pointer_count(
    r2: str, binary: str, func_name: str, metadata_enabled: bool
) -> dict[str, Any]:
    analysis_cmd = "aaa" if metadata_enabled else "aa"
    cmd = "; ".join(
        [
            "a:sla.info >/dev/null",
            analysis_cmd,
            f"s {func_name}",
            "afva",
            "afvj",
        ]
    )
    result = run_r2(r2, binary, cmd)
    out: dict[str, Any] = {"returncode": result.returncode}
    if result.returncode != 0 and result.stderr.strip():
        out["stderr"] = result.stderr.strip()
    try:
        payload = parse_json_payload(result.stdout)
        reg_entries = payload.get("reg", []) if isinstance(payload, dict) else []
        pointer_args = 0
        if isinstance(reg_entries, list):
            for entry in reg_entries:
                if not isinstance(entry, dict):
                    continue
                ty = entry.get("type")
                if isinstance(ty, str) and "*" in ty:
                    pointer_args += 1
        out["pointer_args"] = pointer_args
    except Exception as exc:  # noqa: BLE001
        out["error"] = f"{exc}"
        out["pointer_args"] = 0
    return out


def median_timing(r2: str, metadata_enabled: bool, runs: int) -> dict[str, Any]:
    analysis_cmd = "aaaa" if metadata_enabled else "aa"
    timings = []
    errors = []
    for _ in range(runs):
        cmd = "; ".join(
            [
                "e anal.arch=x86",
                "e arch.bits=64",
                "a:sla.info >/dev/null",
                analysis_cmd,
            ]
        )
        result = run_r2(r2, "/bin/ls", cmd)
        timings.append(result.elapsed_s)
        if result.returncode != 0:
            errors.append(
                {
                    "returncode": result.returncode,
                    "stderr": result.stderr.strip(),
                }
            )
    return {
        "runs": runs,
        "samples_s": [round(t, 6) for t in timings],
        "median_s": round(statistics.median(timings), 6) if timings else None,
        "errors": errors,
    }


def main() -> int:
    args = parse_args()
    vuln_bin = str(vuln_test_path())

    comment_counts = {
        "vuln_test": {
            "meta_on": collect_comment_metrics(args.r2, vuln_bin, True, force_x86=False),
            "meta_off": collect_comment_metrics(args.r2, vuln_bin, False, force_x86=False),
        },
        "bin_ls_forced_x86": {
            "meta_on": collect_comment_metrics(args.r2, "/bin/ls", True, force_x86=True),
            "meta_off": collect_comment_metrics(args.r2, "/bin/ls", False, force_x86=True),
        },
    }

    afvj_counts: dict[str, dict[str, Any]] = {}
    for func in AFVJ_POINTER_FUNCS:
        afvj_counts[func] = {
            "meta_on": collect_afvj_pointer_count(args.r2, vuln_bin, func, True),
            "meta_off": collect_afvj_pointer_count(args.r2, vuln_bin, func, False),
        }

    perf_off = median_timing(args.r2, False, args.runs)
    perf_on = median_timing(args.r2, True, args.runs)
    off_median = perf_off.get("median_s") or 0.0
    on_median = perf_on.get("median_s") or 0.0
    overhead_pct = ((on_median - off_median) / off_median * 100.0) if off_median > 0 else 0.0

    vuln_pass = (
        comment_counts["vuln_test"]["meta_on"]["meta_lines"]
        > comment_counts["vuln_test"]["meta_off"]["meta_lines"]
    )
    ls_pass = (
        comment_counts["bin_ls_forced_x86"]["meta_on"]["meta_lines"]
        > comment_counts["bin_ls_forced_x86"]["meta_off"]["meta_lines"]
    )
    pointer_pass = {
        func: afvj_counts[func]["meta_on"].get("pointer_args", 0)
        >= afvj_counts[func]["meta_off"].get("pointer_args", 0)
        for func in AFVJ_POINTER_FUNCS
    }
    pointer_pass_all = all(pointer_pass.values())
    perf_pass = overhead_pct <= args.max_overhead_pct
    overall_pass = vuln_pass and ls_pass and pointer_pass_all and perf_pass

    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "r2": args.r2,
            "runs": args.runs,
            "max_overhead_pct": args.max_overhead_pct,
            "strict": args.strict,
        },
        "semantic_counts": comment_counts,
        "afvj_pointer_args": afvj_counts,
        "performance": {
            "meta_off": perf_off,
            "meta_on": perf_on,
            "overhead_pct": round(overhead_pct, 4),
            "threshold_pct": args.max_overhead_pct,
        },
        "status": {
            "semantic_meta_lines_vuln_test_pass": vuln_pass,
            "semantic_meta_lines_bin_ls_pass": ls_pass,
            "afvj_pointer_coverage_pass": pointer_pass_all,
            "afvj_pointer_coverage_by_func": pointer_pass,
            "perf_overhead_pass": perf_pass,
            "overall": "PASS" if overall_pass else "FAIL",
        },
    }

    print("Semantic Metadata Advisory Benchmark")
    print(f"  vuln_test meta lines: on={comment_counts['vuln_test']['meta_on']['meta_lines']} off={comment_counts['vuln_test']['meta_off']['meta_lines']}")
    print(
        "  /bin/ls (forced x86) meta lines: "
        f"on={comment_counts['bin_ls_forced_x86']['meta_on']['meta_lines']} "
        f"off={comment_counts['bin_ls_forced_x86']['meta_off']['meta_lines']}"
    )
    print(
		"  /bin/ls native-depth median: "
        f"off={off_median:.6f}s on={on_median:.6f}s overhead={overhead_pct:.2f}%"
    )
    for func in AFVJ_POINTER_FUNCS:
        on_count = afvj_counts[func]["meta_on"].get("pointer_args", 0)
        off_count = afvj_counts[func]["meta_off"].get("pointer_args", 0)
        print(f"  afvj pointer args {func}: on={on_count} off={off_count}")
    print(f"  status: {report['status']['overall']}")

    if args.json_out:
        out_path = Path(args.json_out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print(f"  wrote JSON report: {out_path}")

    if args.strict and not overall_pass:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
