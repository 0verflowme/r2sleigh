#!/usr/bin/env python3
"""Turn whole-binary decompilation dumps into a blessed coverage baseline.

What is scored is one bit per function -- did it render -- plus the typed cause
when it did not. The cause is normalised: counts, addresses and function names
vary between builds and between runs of an unchanged tree, and a baseline that
churns on those is a baseline nobody re-blesses honestly.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

BEGIN = re.compile(r"^R2SLEIGH_COV_BEGIN__(?P<name>.+)__(?P<size>\d+)$")
END = re.compile(r"^R2SLEIGH_COV_END__(?P<name>.+)$")
FALLBACK = re.compile(r"/\* r2dec fallback: skipped decompilation for \S+ \((?P<cause>.*)\) \*/")

# Numbers inside a cause are counts of refused obligations or conflicting
# values. They say how much went wrong, not what, and they move with the
# function's size.
DIGITS = re.compile(r"\d+")


def normalise(cause: str) -> str:
    """The part of a refusal that identifies it across builds.

    The lowering site a refusal now carries is deliberately kept: it is what
    separates two unrelated predicates that used to be counted as one cause.
    Its line number is not, for the same reason equality ignores it -- moving a
    line must not churn a baseline.
    """
    cause = re.sub(r"(\w+\.rs):\d+", r"\1", cause)
    cause = DIGITS.sub("N", cause)
    return " ".join(cause.split())


def parse_dump(path: Path) -> list[dict]:
    functions: list[dict] = []
    current: dict | None = None
    body: list[str] = []
    for line in path.read_text(errors="replace").splitlines():
        begin = BEGIN.match(line.strip())
        if begin:
            current = {"function": begin["name"], "size": int(begin["size"])}
            body = []
            continue
        end = END.match(line.strip())
        if end and current is not None:
            text = "\n".join(body)
            fallback = FALLBACK.search(text)
            current["rendered"] = fallback is None and bool(text.strip())
            current["cause"] = None if fallback is None else normalise(fallback["cause"])
            if not text.strip():
                current["cause"] = "no output"
            functions.append(current)
            current = None
            continue
        if current is not None:
            body.append(line)
    return functions


def collect(artifact_root: Path) -> list[dict]:
    entries: list[dict] = []
    for dump in sorted((artifact_root / "dumps").glob("*.txt")):
        cell = dump.stem
        for function in parse_dump(dump):
            entries.append({"cell": cell, **function})
    return entries


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--clang", default="")
    parser.add_argument("--accept-baseline", action="store_true")
    args = parser.parse_args()

    entries = collect(args.artifact_root)
    if not entries:
        print("no functions were swept", file=sys.stderr)
        return 70

    rendered = sum(1 for entry in entries if entry["rendered"])
    causes = Counter(entry["cause"] for entry in entries if not entry["rendered"])
    measured = {
        "clang": args.clang,
        "functions": len(entries),
        "rendered": rendered,
        "entries": {
            f"{entry['cell']}::{entry['function']}": (
                "rendered" if entry["rendered"] else entry["cause"]
            )
            for entry in entries
        },
    }
    (args.artifact_root / "coverage.json").write_text(json.dumps(measured, indent=2) + "\n")

    print(f"functions: {len(entries)}")
    print(f"rendered:  {rendered} ({rendered * 100 // len(entries)}%)")
    for cause, count in causes.most_common():
        print(f"  {count:4d}  {cause}")

    if args.accept_baseline:
        args.baseline.write_text(json.dumps(measured, indent=2) + "\n")
        print(f"baseline accepted: {args.baseline}")
        return 0

    if not args.baseline.exists():
        print(
            f"no baseline at {args.baseline}; run with --accept-baseline to record one",
            file=sys.stderr,
        )
        return 65

    baseline = json.loads(args.baseline.read_text())
    if baseline.get("clang") != args.clang:
        print(
            "baseline was recorded with a different compiler, so the binaries are "
            f"not the same program:\n  baseline: {baseline.get('clang')}\n  here:     {args.clang}",
            file=sys.stderr,
        )
        return 65

    before = baseline["entries"]
    after = measured["entries"]
    lost = sorted(key for key, value in after.items() if value != "rendered" and before.get(key) == "rendered")
    gained = sorted(key for key, value in after.items() if value == "rendered" and before.get(key) not in (None, "rendered"))
    vanished = sorted(set(before) - set(after))
    appeared = sorted(set(after) - set(before))
    changed = sorted(
        key
        for key, value in after.items()
        if key in before and before[key] != "rendered" and value != "rendered" and before[key] != value
    )

    for key in gained:
        print(f"gained: {key} (was {before[key]})")
    for key in changed:
        print(f"cause changed: {key}: {before[key]} -> {after[key]}")
    for key in appeared:
        print(f"new function: {key} = {after[key]}")

    failed = False
    for key in lost:
        print(f"REGRESSION: {key} rendered in the baseline and now refuses: {after[key]}", file=sys.stderr)
        failed = True
    for key in vanished:
        print(f"MISSING: {key} is in the baseline and was not swept", file=sys.stderr)
        failed = True
    if failed:
        return 1

    if gained or appeared:
        print("coverage improved; re-bless with --accept-baseline to record it")
    print(f"coverage gate: {rendered}/{len(entries)} rendered, no regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
