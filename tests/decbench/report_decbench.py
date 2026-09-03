#!/usr/bin/env python3
"""Report a DecBench sweep without letting refusals disappear from the mean.

The raw DecBench mean is conditional on a decompiler having rendered a function.
This report keeps that useful accuracy number, but also reports a quality mean over
the reference function universe. A refusal contributes zero to the latter.

GED and VJ-GED are distances (zero is perfect), so their all-function number uses
``1 / (1 + distance)``. This gives those metrics the same zero-is-worst quality
scale as byte_match and type_match; filling a refused distance with raw zero would
incorrectly reward it as a perfect graph.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path

US = "r2sleigh"
REFERENCE = "angr"
LOWER_IS_BETTER = {"ged", "vj_ged"}


def function_key(group: dict, function: dict) -> str:
    """Return the globally unique project/binary/opt/function key."""
    return (
        f"{group['project']}/{group['binary']}/{group['opt_level']}"
        f"::{function['function']}"
    )


def group_key(group: dict) -> str:
    return f"{group['project']}/{group['binary']}/{group['opt_level']}"


def cell_key(project: str, opt_level: str) -> str:
    return f"{project}/{opt_level}"


def key_cell(key: str) -> str:
    project, _binary, opt_and_function = key.split("/", 2)
    opt_level = opt_and_function.split("::", 1)[0]
    return cell_key(project, opt_level)


def group_cell(key: str) -> str:
    project, _binary, opt_level = key.split("/", 2)
    return cell_key(project, opt_level)


@dataclass
class Collected:
    rows: dict[str, dict]
    groups: set[str]
    cells: set[str]
    projects: set[str]
    opt_levels: set[str]
    reference_version: str | None


def collect(results: dict) -> Collected:
    rows: dict[str, dict] = {}
    groups: set[str] = set()
    observed_cells: set[str] = set()
    projects: set[str] = set()
    opt_levels: set[str] = set()
    for group in results.get("groups", []):
        groups.add(group_key(group))
        observed_cells.add(cell_key(group["project"], group["opt_level"]))
        projects.add(group["project"])
        opt_levels.add(group["opt_level"])
        for function in group.get("functions", []):
            key = function_key(group, function)
            if key in rows:
                raise ValueError(f"duplicate function result: {key}")
            rows[key] = {
                "decompiled": bool(function.get("decompiled", {}).get(US)),
                "scores": {
                    metric: float(value)
                    for metric, value in (function.get("values", {}).get(US) or {}).items()
                    if value is not None
                },
                "reference_decompiled": bool(
                    function.get("decompiled", {}).get(REFERENCE)
                ),
                "reference": {
                    metric: float(value)
                    for metric, value in (
                        function.get("values", {}).get(REFERENCE) or {}
                    ).items()
                    if value is not None
                },
            }

    sweep = results.get("sweep") or {}
    cells = set(sweep.get("expected_cells") or observed_cells)
    for cell in cells:
        project, opt_level = cell.rsplit("/", 1)
        projects.add(project)
        opt_levels.add(opt_level)
    version = (results.get("decompiler_versions") or {}).get(REFERENCE)
    return Collected(rows, groups, cells, projects, opt_levels, version)


def quality(metric: str, value: float) -> float:
    """Map a rendered metric to the zero-is-worst coverage scale."""
    if metric in LOWER_IS_BETTER:
        return 1.0 / (1.0 + max(0.0, value))
    return value


def _mean(values: list[float]) -> dict:
    return {
        "n": len(values),
        "mean": sum(values) / len(values) if values else None,
    }


def summarise(rows: dict[str, dict]) -> dict:
    metrics = sorted(
        {
            metric
            for row in rows.values()
            for column in ("scores", "reference")
            for metric in row[column]
        }
    )
    metric_summary: dict[str, dict] = {}
    for metric in metrics:
        rendered = [
            row["scores"][metric] for row in rows.values() if metric in row["scores"]
        ]
        reference_rendered = [
            row["reference"][metric]
            for row in rows.values()
            if metric in row["reference"]
        ]
        all_functions = [
            quality(metric, row["scores"][metric]) if metric in row["scores"] else 0.0
            for row in rows.values()
        ]
        reference_all = [
            quality(metric, row["reference"][metric])
            if metric in row["reference"]
            else 0.0
            for row in rows.values()
        ]
        metric_summary[metric] = {
            "direction": "lower_is_better" if metric in LOWER_IS_BETTER else "higher_is_better",
            "rendered": _mean(rendered),
            "all_functions": {
                **_mean(all_functions),
                "refusal_value": 0.0,
                "scale": (
                    "quality=1/(1+distance), higher_is_better"
                    if metric in LOWER_IS_BETTER
                    else "native, higher_is_better"
                ),
            },
            "reference_rendered": _mean(reference_rendered),
            "reference_all_functions": {
                **_mean(reference_all),
                "refusal_value": 0.0,
                "scale": (
                    "quality=1/(1+distance), higher_is_better"
                    if metric in LOWER_IS_BETTER
                    else "native, higher_is_better"
                ),
            },
        }
    total = len(rows)
    rendered = sum(1 for row in rows.values() if row["decompiled"])
    reference_rendered = sum(1 for row in rows.values() if row["reference_decompiled"])
    return {
        "population": {
            "functions": total,
            "rendered": rendered,
            "coverage": rendered / total if total else 0.0,
            "reference_rendered": reference_rendered,
            "reference_coverage": reference_rendered / total if total else 0.0,
        },
        "metrics": metric_summary,
    }


def rows_for_cells(rows: dict[str, dict], cells: set[str]) -> dict[str, dict]:
    return {key: row for key, row in rows.items() if key_cell(key) in cells}


def groups_for_cells(groups: set[str], cells: set[str]) -> set[str]:
    return {key for key in groups if group_cell(key) in cells}


def reference_universe(
    current: Collected, baseline: dict | None
) -> tuple[dict[str, dict], dict]:
    """Fill absent current rows from the cached reference population as refusals."""
    rows = {key: dict(row) for key, row in current.rows.items()}
    before = (baseline or {}).get("functions") or {}
    expected = rows_for_cells(before, current.cells)
    if current.reference_version is not None:
        # A freshly run reference defines its own complete universe. Pulling old-only
        # rows into it would hide a population loss and could mix angr versions.
        return rows, {"expected": len(expected), "absent": []}
    absent = sorted(set(expected) - set(rows))
    for key in absent:
        old = expected[key]
        rows[key] = {
            "decompiled": False,
            "scores": {},
            "reference_decompiled": bool(old.get("reference_decompiled")),
            "reference": dict(old.get("reference") or {}),
        }
    for key, row in rows.items():
        old = before.get(key) or {}
        if not row["reference"]:
            row["reference"] = dict(old.get("reference") or {})
        if not row["reference_decompiled"]:
            row["reference_decompiled"] = bool(old.get("reference_decompiled"))
    return rows, {"expected": len(expected), "absent": absent}


def measured_record(current: Collected, rows: dict[str, dict]) -> dict:
    return {
        "schema_version": 2,
        "reference": {
            "decompiler": REFERENCE,
            "version": current.reference_version,
        },
        "selection": {
            "projects": sorted(current.projects),
            "opt_levels": sorted(current.opt_levels),
            "cells": sorted(current.cells),
        },
        "groups": sorted(current.groups),
        "functions": dict(sorted(rows.items())),
        "summary": summarise(rows),
    }


def merge_baseline(old: dict | None, measured: dict) -> dict:
    """Replace measured cells while preserving other completed shards."""
    old = old or {}
    new_version = measured["reference"]["version"]
    old_version = (old.get("reference") or {}).get("version")
    if old_version and new_version and old_version != new_version:
        # Reference scores from different angr versions are not one population.
        old = {}

    cells = set(measured["selection"]["cells"])
    functions = {
        key: row
        for key, row in (old.get("functions") or {}).items()
        if key_cell(key) not in cells
    }
    functions.update(measured["functions"])
    groups = {key for key in (old.get("groups") or []) if group_cell(key) not in cells}
    groups.update(measured["groups"])
    all_cells = {key_cell(key) for key in functions}
    projects = {cell.rsplit("/", 1)[0] for cell in all_cells}
    opt_levels = {cell.rsplit("/", 1)[1] for cell in all_cells}
    reference_version = new_version or old_version
    return {
        "schema_version": 2,
        "reference": {"decompiler": REFERENCE, "version": reference_version},
        "selection": {
            "projects": sorted(projects),
            "opt_levels": sorted(opt_levels),
            "cells": sorted(all_cells),
        },
        "groups": sorted(groups),
        "functions": dict(sorted(functions.items())),
        "summary": summarise(functions),
    }


def _fmt_mean(data: dict) -> str:
    value = data["mean"]
    return "n/a" if value is None else f"{value:.3f}"


def print_summary(measured: dict, raw_count: int, reference_fill: dict) -> None:
    population = measured["summary"]["population"]
    selection = measured["selection"]
    print(
        "population: "
        f"{len(selection['projects'])} projects, {len(selection['cells'])} project/opt cells, "
        f"{len(measured['groups'])} binaries, {population['functions']} functions"
    )
    print(
        f"functions observed in current result: {raw_count}; "
        f"reference-only refusals filled: {len(reference_fill['absent'])}"
    )
    print(
        f"coverage: {US} {population['rendered']}/{population['functions']} "
        f"({population['coverage']:.1%}); {REFERENCE} "
        f"{population['reference_rendered']}/{population['functions']} "
        f"({population['reference_coverage']:.1%})"
    )
    print("metrics: rendered mean | all-function quality mean (refusal=0)")
    for metric, data in measured["summary"]["metrics"].items():
        rendered = data["rendered"]
        all_functions = data["all_functions"]
        ref_rendered = data["reference_rendered"]
        ref_all = data["reference_all_functions"]
        suffix = " [distance -> 1/(1+d) for all]" if metric in LOWER_IS_BETTER else ""
        print(
            f"  {metric:11} {US} {_fmt_mean(rendered)} over {rendered['n']} | "
            f"{_fmt_mean(all_functions)} over {all_functions['n']}; "
            f"{REFERENCE} {_fmt_mean(ref_rendered)} over {ref_rendered['n']} | "
            f"{_fmt_mean(ref_all)} over {ref_all['n']}{suffix}"
        )


def compare(measured: dict, baseline: dict) -> int:
    before = rows_for_cells(
        baseline.get("functions") or {}, set(measured["selection"]["cells"])
    )
    rows = measured["functions"]
    before_summary = summarise(before)
    now_summary = measured["summary"]
    bp = before_summary["population"]
    np = now_summary["population"]
    print(
        "comparison populations: "
        f"baseline {bp['rendered']}/{bp['functions']} rendered; "
        f"current {np['rendered']}/{np['functions']} rendered"
    )

    worse: list[str] = []
    missing = sorted(set(before) - set(rows))
    added = sorted(set(rows) - set(before))
    if missing:
        print(
            f"REGRESSION: {len(missing)} baseline functions left the population",
            file=sys.stderr,
        )
        for key in missing[:20]:
            print(f"  missing function: {key}", file=sys.stderr)
        worse.extend(missing)
    if added:
        print(f"new population: {len(added)} functions")

    for key, row in sorted(rows.items()):
        was = before.get(key)
        if was is None:
            continue
        if was["decompiled"] and not row["decompiled"]:
            print(f"REGRESSION: {key} was decompiled and now refuses", file=sys.stderr)
            worse.append(key)
        for metric, value in sorted(row["scores"].items()):
            old = was.get("scores", {}).get(metric)
            if old is None:
                continue
            improved = value < old if metric in LOWER_IS_BETTER else value > old
            declined = value > old if metric in LOWER_IS_BETTER else value < old
            if improved:
                print(f"gained: {key} {metric} {old:.3f} -> {value:.3f}")
            elif declined:
                print(
                    f"REGRESSION: {key} {metric} {old:.3f} -> {value:.3f}",
                    file=sys.stderr,
                )
                worse.append(f"{key} {metric}")
    if worse:
        print(f"{len(worse)} regressions", file=sys.stderr)
        return 1
    print("decbench: no regressions")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--accept-baseline", action="store_true")
    args = parser.parse_args()

    try:
        current = collect(json.loads(args.results.read_text()))
    except (KeyError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(f"invalid result set: {exc}", file=sys.stderr)
        return 70
    baseline = json.loads(args.baseline.read_text()) if args.baseline.exists() else None
    rows, reference_fill = reference_universe(current, baseline)
    if not rows:
        print(
            "the run contains no functions and no cached reference universe",
            file=sys.stderr,
        )
        return 70
    measured = measured_record(current, rows)
    if measured["reference"]["version"] is None and baseline:
        measured["reference"]["version"] = (baseline.get("reference") or {}).get(
            "version"
        )

    expected_groups = groups_for_cells(
        set((baseline or {}).get("groups") or []), current.cells
    )
    missing_groups = sorted(expected_groups - current.groups)
    print_summary(measured, len(current.rows), reference_fill)
    if missing_groups:
        print(
            f"ERROR: {len(missing_groups)} reference binary groups are absent from this sweep",
            file=sys.stderr,
        )
        for key in missing_groups[:20]:
            print(f"  missing binary: {key}", file=sys.stderr)
        return 70

    if args.accept_baseline:
        accepted = merge_baseline(baseline, measured)
        args.baseline.write_text(json.dumps(accepted, indent=2, sort_keys=True) + "\n")
        print(f"baseline accepted: {args.baseline}")
        return 0

    if baseline is None:
        print(
            f"no baseline at {args.baseline}; run with --accept-baseline",
            file=sys.stderr,
        )
        return 65
    return compare(measured, baseline)


if __name__ == "__main__":
    raise SystemExit(main())
