#!/usr/bin/env python3
"""Merge independent DecBench project/shard results into one checked result set."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def merge(payloads: list[dict], expected_cells: set[str] | None = None) -> dict:
    groups: dict[str, dict] = {}
    decompilers: set[str] = set()
    metrics: set[str] = set()
    versions: dict[str, str] = {}
    perfect_values: dict[str, float] = {}
    decompiler_cells: dict[str, set[str]] = {}
    for payload in payloads:
        payload_decompilers = set(payload.get("decompilers") or [])
        payload_groups = payload.get("groups") or []
        payload_cells = {
            f"{group['project']}/{group['opt_level']}" for group in payload_groups
        }
        decompilers.update(payload_decompilers)
        for decompiler in payload_decompilers:
            decompiler_cells.setdefault(decompiler, set()).update(payload_cells)
        metrics.update(payload.get("metrics") or [])
        perfect_values.update(payload.get("perfect_values") or {})
        for decompiler, version in (payload.get("decompiler_versions") or {}).items():
            old = versions.get(decompiler)
            if old is not None and old != version:
                raise ValueError(
                    f"mixed {decompiler} versions: {old!r} and {version!r}"
                )
            versions[decompiler] = version
        for group in payload_groups:
            key = f"{group['project']}/{group['binary']}/{group['opt_level']}"
            if key in groups:
                raise ValueError(f"duplicate binary group: {key}")
            groups[key] = group

    actual_cells = {
        f"{group['project']}/{group['opt_level']}" for group in groups.values()
    }
    expected_cells = set(expected_cells or actual_cells)
    missing_cells = sorted(expected_cells - actual_cells)
    unexpected_cells = sorted(actual_cells - expected_cells)
    if missing_cells or unexpected_cells:
        details = []
        if missing_cells:
            details.append(f"missing project/opt cells: {', '.join(missing_cells)}")
        if unexpected_cells:
            details.append(f"unexpected project/opt cells: {', '.join(unexpected_cells)}")
        raise ValueError("; ".join(details))

    return {
        "schema_version": max(
            (p.get("schema_version", 1) for p in payloads), default=1
        ),
        "decompilers": sorted(decompilers),
        "decompiler_versions": dict(sorted(versions.items())),
        "metrics": sorted(metrics),
        "perfect_values": dict(sorted(perfect_values.items())),
        "groups": [groups[key] for key in sorted(groups)],
        "sweep": {
            "expected_cells": sorted(expected_cells),
            "completed_cells": sorted(actual_cells),
            "decompiler_cells": {
                decompiler: sorted(cells)
                for decompiler, cells in sorted(decompiler_cells.items())
            },
            "input_results": len(payloads),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--expected-cell",
        action="append",
        default=[],
        metavar="PROJECT/OPT",
    )
    args = parser.parse_args()
    try:
        payloads = [json.loads(path.read_text()) for path in args.input]
        merged = merge(payloads, set(args.expected_cell) or None)
    except (KeyError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(f"cannot merge DecBench results: {exc}", file=sys.stderr)
        return 70
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n")
    print(
        f"merged {len(payloads)} results: {len(merged['groups'])} binary groups, "
        f"{len(merged['sweep']['completed_cells'])} project/opt cells"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
