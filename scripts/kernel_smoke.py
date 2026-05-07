#!/usr/bin/env python3
"""Kernel-driven smoke harness for paired r2sleigh/radare2 validation.

The harness intentionally does not ship or discover Apple kernel binaries. Point
R2SLEIGH_KERNELCACHE at a local kernelcache when running this manually.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_TARGETS = (
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


@dataclass
class CmdResult:
    returncode: int
    stdout: str
    stderr: str
    elapsed_s: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run deterministic r2sleigh smoke checks over a local Apple kernelcache."
    )
    parser.add_argument(
        "--kernel",
        default=os.environ.get("R2SLEIGH_KERNELCACHE", ""),
        help="kernelcache path, defaults to R2SLEIGH_KERNELCACHE",
    )
    parser.add_argument(
        "--r2",
        default=os.environ.get(
            "R2R_RADARE2", "/Users/priyanshu/code/radare2/binr/radare2/radare2"
        ),
        help="radare2 executable path",
    )
    parser.add_argument(
        "--analysis",
        choices=("aa", "aaa", "aaaa"),
        default="aaaa",
        help="native radare2 analysis depth to exercise",
    )
    parser.add_argument(
        "--targets",
        default=",".join(DEFAULT_TARGETS),
        help="comma-separated symbol names to probe",
    )
    parser.add_argument(
        "--out",
        default="/tmp/r2sleigh-kernel-smoke.json",
        help="JSON report output path",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=420,
        help="per-radare2 command timeout in seconds",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="return non-zero when any matched target has a failing command",
    )
    return parser.parse_args()


def run_r2(r2: str, binary: Path, cmd: str, timeout_s: int) -> CmdResult:
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
    proc = subprocess.run(
        argv,
        capture_output=True,
        text=True,
        timeout=timeout_s,
        check=False,
    )
    return CmdResult(
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
        elapsed_s=time.perf_counter() - start,
    )


def parse_json_payload(text: str) -> Any:
    stripped = text.strip()
    if not stripped:
        raise ValueError("empty output")
    for idx, ch in enumerate(stripped):
        if ch not in "[{":
            continue
        try:
            return json.loads(stripped[idx:])
        except json.JSONDecodeError:
            continue
    raise ValueError("no JSON payload found")


def normalize_symbol(name: str) -> str:
    for prefix in ("sym.", "dbg.", "imp."):
        if name.startswith(prefix):
            name = name[len(prefix) :]
    return name.lstrip("_").lower()


def discover_functions(
    r2: str, kernel: Path, analysis: str, timeout_s: int
) -> tuple[list[dict[str, Any]], CmdResult]:
    result = run_r2(r2, kernel, f"a:sla >/dev/null; {analysis}; aflj", timeout_s)
    functions: list[dict[str, Any]] = []
    if result.returncode != 0:
        return functions, result
    try:
        payload = parse_json_payload(result.stdout)
    except ValueError:
        return functions, result
    if not isinstance(payload, list):
        return functions, result
    for item in payload:
        if not isinstance(item, dict):
            continue
        name = item.get("name")
        offset = item.get("offset")
        blocks = item.get("nbbs")
        size = item.get("size")
        if isinstance(name, str) and isinstance(offset, int):
            functions.append(
                {
                    "name": name,
                    "addr": offset,
                    "blocks": blocks if isinstance(blocks, int) else None,
                    "size": size if isinstance(size, int) else None,
                }
            )
    functions.sort(key=lambda f: (f["addr"], f["name"]))
    return functions, result


def choose_targets(
    functions: list[dict[str, Any]], requested: list[str]
) -> list[dict[str, Any]]:
    by_norm: dict[str, list[dict[str, Any]]] = {}
    for fcn in functions:
        by_norm.setdefault(normalize_symbol(fcn["name"]), []).append(fcn)

    selected: list[dict[str, Any]] = []
    seen_addrs: set[int] = set()
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
        selected.append(
            {
                "requested": target,
                "found": True,
                "name": fcn["name"],
                "addr": fcn["addr"],
                "blocks": fcn.get("blocks"),
                "size": fcn.get("size"),
            }
        )
    return selected


def summarize_text(text: str, max_lines: int = 80) -> dict[str, Any]:
    lines = text.splitlines()
    return {
        "sha256": hashlib.sha256(text.encode("utf-8", "replace")).hexdigest(),
        "bytes": len(text.encode("utf-8", "replace")),
        "lines": len(lines),
        "preview": lines[:max_lines],
        "truncated": len(lines) > max_lines,
    }


def collect_target(
    r2: str, kernel: Path, analysis: str, target: dict[str, Any], timeout_s: int
) -> dict[str, Any]:
    if not target.get("found"):
        return target
    addr = target["addr"]
    prefix = f"a:sla >/dev/null; {analysis}; s 0x{addr:x}; af"
    commands = {
        "decompile_sla": "a:sla.dec",
        "decompile_pdd": "pdd",
        "decompile_pdD": "pdD",
        "types": "a:sla.debug.types",
        "profile": "a:sla.debug.profilej",
        "symex": "a:sym.explore",
    }
    out: dict[str, Any] = dict(target)
    out["commands"] = {}
    for name, command in commands.items():
        result = run_r2(r2, kernel, f"{prefix}; {command}", timeout_s)
        entry: dict[str, Any] = {
            "returncode": result.returncode,
            "elapsed_s": round(result.elapsed_s, 6),
            "stdout": summarize_text(result.stdout),
        }
        if result.stderr.strip():
            entry["stderr"] = summarize_text(result.stderr, max_lines=40)
        if name in {"profile", "types", "symex"} and result.stdout.strip():
            try:
                entry["json_kind"] = type(parse_json_payload(result.stdout)).__name__
            except ValueError as exc:
                entry["json_error"] = str(exc)
        out["commands"][name] = entry
    return out


def main() -> int:
    args = parse_args()
    report_path = Path(args.out)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    if not args.kernel:
        report = {
            "schema": 1,
            "status": "skipped",
            "reason": "R2SLEIGH_KERNELCACHE is not set",
            "generated_at": datetime.now(timezone.utc).isoformat(),
        }
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(f"kernel smoke skipped; wrote {report_path}")
        return 0

    kernel = Path(args.kernel)
    if not kernel.exists():
        print(f"kernel smoke failed: missing kernelcache {kernel}", file=sys.stderr)
        return 2

    requested_targets = [target.strip() for target in args.targets.split(",") if target.strip()]
    functions, discovery = discover_functions(args.r2, kernel, args.analysis, args.timeout)
    selected = choose_targets(functions, requested_targets)
    collected = [
        collect_target(args.r2, kernel, args.analysis, target, args.timeout)
        for target in selected
    ]
    failures = [
        {
            "target": item.get("name") or item.get("requested"),
            "command": command,
            "returncode": result.get("returncode"),
        }
        for item in collected
        for command, result in item.get("commands", {}).items()
        if result.get("returncode") != 0
    ]
    report = {
        "schema": 1,
        "status": "failed" if failures else "ok",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "r2": args.r2,
        "kernel": str(kernel),
        "analysis": args.analysis,
        "discovery": {
            "returncode": discovery.returncode,
            "elapsed_s": round(discovery.elapsed_s, 6),
            "function_count": len(functions),
            "stdout": summarize_text(discovery.stdout, max_lines=20),
        },
        "requested_targets": requested_targets,
        "targets": collected,
        "failures": failures,
    }
    if discovery.stderr.strip():
        report["discovery"]["stderr"] = summarize_text(discovery.stderr, max_lines=20)
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"kernel smoke {report['status']}; wrote {report_path}")
    if failures and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
