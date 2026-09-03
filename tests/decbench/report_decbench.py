#!/usr/bin/env python3
"""Compare a DecBench run with the recorded one, per function and per metric.

The scoreboard's aggregate mean is not enough to act on. A mean that falls can
mean one function regressed badly or that a function which used to refuse now
renders imperfectly, and those call for opposite responses. So the record is
per function per metric, and a change names the function.

`decompiled` is recorded alongside the scores because a refused function has no
score at all, and the difference between "refused" and "scored zero" is the
difference between a coverage problem and a correctness one.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

US = "r2sleigh"
# Every metric here is "closer to zero is worse" except ged, where the score is
# an edit distance and zero is a perfect match.
LOWER_IS_BETTER = {"ged"}


def collect(results: dict) -> dict:
    rows: dict[str, dict] = {}
    for group in results.get("groups", []):
        for function in group.get("functions", []):
            key = f"{group['binary']}/{group['opt_level']}::{function['function']}"
            rows[key] = {
                "decompiled": bool(function.get("decompiled", {}).get(US)),
                "scores": {
                    metric: value
                    for metric, value in (function.get("values", {}).get(US) or {}).items()
                    if value is not None
                },
                "reference": {
                    metric: value
                    for metric, value in (function.get("values", {}).get("angr") or {}).items()
                    if value is not None
                },
            }
    return rows


def summarise(rows: dict) -> dict:
    metrics: dict[str, dict] = {}
    for row in rows.values():
        for metric, value in row["scores"].items():
            metrics.setdefault(metric, {"n": 0, "total": 0.0})
            metrics[metric]["n"] += 1
            metrics[metric]["total"] += value
    return {
        metric: {"n": data["n"], "mean": data["total"] / data["n"]}
        for metric, data in sorted(metrics.items())
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--accept-baseline", action="store_true")
    args = parser.parse_args()

    rows = collect(json.loads(args.results.read_text()))
    if not rows:
        print("the run scored no functions", file=sys.stderr)
        return 70
    measured = {"schema_version": 1, "functions": rows, "summary": summarise(rows)}

    rendered = sum(1 for row in rows.values() if row["decompiled"])
    print(f"functions: {len(rows)}, decompiled by {US}: {rendered}")
    for metric, data in measured["summary"].items():
        reference = [
            row["reference"][metric] for row in rows.values() if metric in row["reference"]
        ]
        against = f", angr {sum(reference) / len(reference):.3f} over {len(reference)}" if reference else ""
        print(f"  {metric:11} {data['mean']:.3f} over {data['n']}{against}")

    if args.accept_baseline:
        args.baseline.write_text(json.dumps(measured, indent=2, sort_keys=True) + "\n")
        print(f"baseline accepted: {args.baseline}")
        return 0

    if not args.baseline.exists():
        print(f"no baseline at {args.baseline}; run with --accept-baseline", file=sys.stderr)
        return 65

    baseline = json.loads(args.baseline.read_text())
    before = baseline["functions"]
    worse: list[str] = []
    for key, row in sorted(rows.items()):
        was = before.get(key)
        if was is None:
            print(f"new function: {key}")
            continue
        if was["decompiled"] and not row["decompiled"]:
            print(f"REGRESSION: {key} was decompiled and now refuses", file=sys.stderr)
            worse.append(key)
        for metric, value in sorted(row["scores"].items()):
            old = was["scores"].get(metric)
            if old is None:
                continue
            improved = value < old if metric in LOWER_IS_BETTER else value > old
            declined = value > old if metric in LOWER_IS_BETTER else value < old
            if improved:
                print(f"gained: {key} {metric} {old:.3f} -> {value:.3f}")
            elif declined:
                print(f"REGRESSION: {key} {metric} {old:.3f} -> {value:.3f}", file=sys.stderr)
                worse.append(f"{key} {metric}")
    if worse:
        print(f"{len(worse)} regressions", file=sys.stderr)
        return 1
    print("decbench: no regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
