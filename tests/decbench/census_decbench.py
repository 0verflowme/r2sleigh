#!/usr/bin/env python3
"""Rank refusal causes across a sweep's per-binary censuses.

The benchmark's own results carry one boolean per function, so a sweep answers
*how many* functions were declined and never *why*.  Each binary writes a
census beside the run (``r2sleigh-refusals-*.json``); this reads a directory of
them and reports the ranking that coverage work is supposed to be planned
against.

Two distinctions the report keeps, because collapsing either one has already
misdirected a session's work:

*Harness failures are not refusals.*  A cause prefixed ``harness:`` is this
tooling saying it never got to ask -- a crashed ``r2``, a plugin that would not
load.  Counting those as the decompiler declining is how five zlib binaries
reporting zero functions read as an unusually shy decompiler while holding 68%
of the benchmark's refusals.  They are ranked separately and, being tooling
defects rather than proof gaps, ranked first.

*Causes compose multiplicatively.*  A census records only the first cause per
function, so ``P(render) = prod(1 - p_i)`` and closing the top cause unmasks
the next.  A share here is an upper bound on what closing that cause buys, and
the ranking must be retaken after each one is closed rather than planned once.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import sys

HARNESS = "harness:"


def _cell(payload: dict) -> str:
    """The project/optimization cell a census belongs to.

    Derived from the recorded build path rather than asked for, because the
    adapter is handed a path and nothing else.  decbench lays binaries out as
    ``<out>/<opt>/<project>/compiled/<binary>``; when the path does not have
    that shape the cell is reported as unknown rather than guessed.
    """
    raw = payload.get("binary_path")
    if not raw:
        return "unknown"
    parts = pathlib.PurePosixPath(raw).parts
    if len(parts) >= 4 and parts[-2] == "compiled":
        return f"{parts[-3]}/{parts[-4]}"
    return "unknown"


def load(directory: pathlib.Path) -> list[dict]:
    payloads = []
    for path in sorted(directory.rglob("r2sleigh-refusals-*.json")):
        try:
            payloads.append(json.loads(path.read_text(encoding="utf-8")))
        except (OSError, ValueError) as exc:
            print(f"skipped {path.name}: {exc}", file=sys.stderr)
    return payloads


def report(payloads: list[dict], top: int) -> None:
    rendered = sum(p.get("rendered", 0) for p in payloads)
    declined = sum(p.get("declined", 0) for p in payloads)
    observed = rendered + declined
    if observed == 0:
        print("no functions observed in any census", file=sys.stderr)
        return

    by_cell: dict[str, list[int]] = collections.defaultdict(lambda: [0, 0])
    causes: collections.Counter[str] = collections.Counter()
    for payload in payloads:
        cell = by_cell[_cell(payload)]
        cell[0] += payload.get("rendered", 0)
        cell[1] += payload.get("declined", 0)
        causes.update(payload.get("causes", {}))

    print(f"binaries   {len(payloads)}")
    print(f"observed   {observed} functions")
    print(f"coverage   {rendered}/{observed} = {rendered / observed:.3f}")
    print()

    print("by cell")
    for name in sorted(by_cell):
        rend, decl = by_cell[name]
        total = rend + decl
        share = rend / total if total else 0.0
        print(f"  {name:<24} {rend:>5}/{total:<5} = {share:.3f}")
    print()

    harness = [(c, n) for c, n in causes.items() if c.startswith(HARNESS)]
    proof = [(c, n) for c, n in causes.items() if not c.startswith(HARNESS)]

    for title, rows in (("harness failures", harness), ("refusal causes", proof)):
        lost = sum(n for _, n in rows)
        print(f"{title}: {lost} functions, {lost / observed:.3f} of all observed")
        for cause, count in sorted(rows, key=lambda kv: (-kv[1], kv[0]))[:top]:
            print(f"  {count:>5}  {count / observed:.3f}  {cause}")
        if not rows:
            print("  none")
        print()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=pathlib.Path,
                        help="directory holding r2sleigh-refusals-*.json")
    parser.add_argument("--top", type=int, default=20,
                        help="how many causes to list per category")
    args = parser.parse_args()
    payloads = load(args.directory)
    if not payloads:
        print(f"no census files under {args.directory}", file=sys.stderr)
        return 1
    report(payloads, args.top)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
