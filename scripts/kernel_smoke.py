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

JSON_COMMANDS = frozenset({"ssa_function_report"})
DECOMPILER_COMMANDS = frozenset({"decompile_sla", "decompile_pdd", "decompile_pdD"})
DECOMPILER_FALLBACK_MARKERS = (
    "r2dec fallback:",
    "r2dec: decompilation panicked",
    "r2dec: failed to spawn",
    "skipped decompilation",
    "r2pm -ci r2dec",
)


@dataclass
class CmdResult:
    returncode: int
    stdout: str
    stderr: str
    elapsed_s: float


def default_r2_path() -> str:
    for env_name in ("R2SLEIGH_E2E_RADARE2", "R2R_RADARE2"):
        value = os.environ.get(env_name, "").strip()
        if value:
            return value
    for candidate in (
        "../radare2/binr/radare2/radare2",
        "../../radare2/binr/radare2/radare2",
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
        description="Run deterministic r2sleigh smoke checks over a local Apple kernelcache."
    )
    parser.add_argument(
        "--kernel",
        default=os.environ.get("R2SLEIGH_KERNELCACHE", ""),
        help="kernelcache path, defaults to R2SLEIGH_KERNELCACHE",
    )
    parser.add_argument(
        "--r2",
        default=default_r2_path(),
        help="radare2 executable path",
    )
    parser.add_argument(
        "--plugin-dir",
        default=default_plugin_dir(),
        help="isolated radare2 plugin directory, defaults to R2SLEIGH_PLUGIN_DIR/R2R_PLUGIN_DIR",
    )
    parser.add_argument(
        "--tmpdir",
        default=os.environ.get("R2SLEIGH_KERNEL_SMOKE_TMPDIR", "/tmp/r2sleigh-kernel-smoke-tmp"),
        help="temporary HOME/XDG/TMP root for the radare2 subprocess",
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
        help="return non-zero when discovery, target matching, JSON validation, or commands fail",
    )
    parser.add_argument(
        "--include-sensitive",
        action="store_true",
        help="include local kernel paths and stdout/stderr previews in the JSON report",
    )
    return parser.parse_args()


def build_r2_env(plugin_dir: str, tmpdir: Path | None) -> dict[str, str]:
    env = os.environ.copy()
    if plugin_dir:
        env["R2_USER_PLUGINS"] = plugin_dir
        env["R2_LIBR_PLUGINS"] = plugin_dir
    if tmpdir is not None:
        tmpdir.mkdir(parents=True, exist_ok=True)
        xdg_data = tmpdir / "xdg-data"
        xdg_data.mkdir(parents=True, exist_ok=True)
        env["TMPDIR"] = str(tmpdir)
        env["TMP"] = str(tmpdir)
        env["TEMP"] = str(tmpdir)
        env["XDG_DATA_HOME"] = str(xdg_data)
        env["HOME"] = str(tmpdir / "home")
        Path(env["HOME"]).mkdir(parents=True, exist_ok=True)
    return env


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


def parse_base0_int(value: Any) -> int | None:
    if not isinstance(value, str):
        return None
    try:
        return int(value, 0)
    except ValueError:
        return None


def redacted_path(path: Path) -> str:
    return f"<redacted:{path.name}>"


def normalize_symbol(name: str) -> str:
    for prefix in ("sym.", "dbg.", "imp."):
        if name.startswith(prefix):
            name = name[len(prefix) :]
    return name.lstrip("_").lower()


def discover_functions(
    r2: str,
    kernel: Path,
    analysis: str,
    timeout_s: int,
    env: dict[str, str] | None = None,
) -> tuple[list[dict[str, Any]], CmdResult]:
    result = run_r2(r2, kernel, f"a:sla >/dev/null; {analysis}; aflj", timeout_s, env=env)
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


def summarize_text(text: str, max_lines: int = 80, include_preview: bool = False) -> dict[str, Any]:
    lines = text.splitlines()
    summary: dict[str, Any] = {
        "sha256": hashlib.sha256(text.encode("utf-8", "replace")).hexdigest(),
        "bytes": len(text.encode("utf-8", "replace")),
        "lines": len(lines),
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


def collect_target(
    r2: str,
    kernel: Path,
    analysis: str,
    target: dict[str, Any],
    timeout_s: int,
    include_sensitive: bool,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    if not target.get("found"):
        return target
    addr = target["addr"]
    prefix = f"a:sla >/dev/null; {analysis}; s 0x{addr:x}; af"
    commands = {
        "decompile_sla": "pdd",
        "decompile_pdd": "pdd",
        "decompile_pdD": "pdD",
        "ssa_function_report": "a:sla.debug.ssa.func",
    }
    out: dict[str, Any] = dict(target)
    out["commands"] = {}
    for name, command in commands.items():
        result = run_r2(r2, kernel, f"{prefix}; {command}", timeout_s, env=env)
        entry: dict[str, Any] = {
            "returncode": result.returncode,
            "elapsed_s": round(result.elapsed_s, 6),
            "stdout": summarize_text(result.stdout, include_preview=include_sensitive),
        }
        if result.stderr.strip():
            entry["stderr"] = summarize_text(
                result.stderr, max_lines=40, include_preview=include_sensitive
            )
        if name in JSON_COMMANDS:
            try:
                payload = parse_json_payload(result.stdout)
                entry["json_kind"] = type(payload).__name__
                if name == "ssa_function_report" and isinstance(payload, dict):
                    blocks = payload.get("blocks")
                    function_entry = payload.get("entry")
                    entry_hex_addr = parse_base0_int(payload.get("entry_hex"))
                    num_blocks = payload.get("num_blocks")
                    schema_version = payload.get("schema_version")
                    blocks_well_formed = (
                        isinstance(blocks, list)
                        and bool(blocks)
                        and all(
                            isinstance(block, dict)
                            and type(block.get("addr")) is int
                            and parse_base0_int(block.get("addr_hex"))
                            == block.get("addr")
                            and type(block.get("size")) is int
                            and block.get("size") > 0
                            and isinstance(block.get("phis"), list)
                            and isinstance(block.get("ops"), list)
                            for block in blocks
                        )
                    )
                    entry_block_present = blocks_well_formed and any(
                        block.get("addr") == function_entry for block in blocks
                    )
                    prepared = payload.get("prepared")
                    entry["ssa_report_valid"] = (
                        type(schema_version) is int
                        and schema_version == 2
                        and type(function_entry) is int
                        and function_entry == addr
                        and entry_hex_addr == addr
                        and type(num_blocks) is int
                        and num_blocks > 0
                        and isinstance(blocks, list)
                        and num_blocks == len(blocks)
                        and blocks_well_formed
                        and entry_block_present
                        and isinstance(prepared, dict)
                        and isinstance(prepared.get("formal_parameters"), list)
                        and isinstance(prepared.get("parameter_addresses"), list)
                    )
            except ValueError as exc:
                entry["json_error"] = str(exc)
        if name in DECOMPILER_COMMANDS:
            marker = decompiler_fallback_marker(result.stdout)
            if marker is not None:
                entry["fallback_marker"] = marker
        out["commands"][name] = entry
    return out


def collect_failures(
    functions: list[dict[str, Any]],
    discovery: CmdResult,
    collected: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    if discovery.returncode != 0:
        failures.append(
            {
                "kind": "command_return",
                "target": "discovery",
                "command": "aflj",
                "returncode": discovery.returncode,
            }
        )
    if len(functions) == 0:
        failures.append(
            {
                "kind": "zero_functions",
                "target": "discovery",
                "command": "aflj",
            }
        )
    for item in collected:
        target_name = item.get("name") or item.get("requested")
        if not item.get("found", True):
            failures.append(
                {
                    "kind": "missing_target",
                    "target": target_name,
                }
            )
            continue
        for command, result in item.get("commands", {}).items():
            if result.get("returncode") != 0:
                failures.append(
                    {
                        "kind": "command_return",
                        "target": target_name,
                        "command": command,
                        "returncode": result.get("returncode"),
                    }
                )
            if command in JSON_COMMANDS and result.get("json_error"):
                failures.append(
                    {
                        "kind": "json_parse",
                        "target": target_name,
                        "command": command,
                        "error": result.get("json_error"),
                    }
                )
            if (
                command == "ssa_function_report"
                and not result.get("json_error")
                and result.get("ssa_report_valid") is not True
            ):
                failures.append(
                    {
                        "kind": "invalid_ssa_function_report",
                        "target": target_name,
                        "command": command,
                    }
                )
            if command in DECOMPILER_COMMANDS and result.get("fallback_marker"):
                failures.append(
                    {
                        "kind": "decompiler_fallback",
                        "target": target_name,
                        "command": command,
                        "marker": result.get("fallback_marker"),
                    }
                )
    return failures


def write_report(path: Path, report: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


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
        write_report(report_path, report)
        print(f"kernel smoke skipped; wrote {report_path}")
        return 0

    kernel = Path(args.kernel)
    if not kernel.exists():
        report = {
            "schema": 1,
            "status": "failed",
            "reason": "missing kernelcache",
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "kernel": str(kernel) if args.include_sensitive else redacted_path(kernel),
        }
        write_report(report_path, report)
        print(
            "kernel smoke failed: missing kernelcache "
            f"{kernel if args.include_sensitive else redacted_path(kernel)}",
            file=sys.stderr,
        )
        return 2

    requested_targets = [target.strip() for target in args.targets.split(",") if target.strip()]
    env = build_r2_env(args.plugin_dir, Path(args.tmpdir) if args.tmpdir else None)
    functions, discovery = discover_functions(
        args.r2, kernel, args.analysis, args.timeout, env=env
    )
    selected = choose_targets(functions, requested_targets)
    collected = [
        collect_target(
            args.r2,
            kernel,
            args.analysis,
            target,
            args.timeout,
            args.include_sensitive,
            env=env,
        )
        for target in selected
    ]
    failures = collect_failures(functions, discovery, collected)
    report = {
        "schema": 1,
        "status": "failed" if failures else "ok",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "r2": args.r2,
        "kernel": str(kernel) if args.include_sensitive else redacted_path(kernel),
        "analysis": args.analysis,
        "discovery": {
            "returncode": discovery.returncode,
            "elapsed_s": round(discovery.elapsed_s, 6),
            "function_count": len(functions),
            "stdout": summarize_text(
                discovery.stdout, max_lines=20, include_preview=args.include_sensitive
            ),
        },
        "requested_targets": requested_targets,
        "targets": collected,
        "failures": failures,
    }
    if discovery.stderr.strip():
        report["discovery"]["stderr"] = summarize_text(
            discovery.stderr, max_lines=20, include_preview=args.include_sensitive
        )
    write_report(report_path, report)
    print(f"kernel smoke {report['status']}; wrote {report_path}")
    if failures and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
