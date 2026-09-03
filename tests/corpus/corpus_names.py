#!/usr/bin/env python3
"""Print one corpus's scored functions and its helper callees.

verify_rendering.py is the one place that knows what a corpus is made of. The
sweep and the run script both need the same lists, and a second copy of them in
shell is a second answerer that drifts: a function added to the specs but not to
the sweep is measured as `missing` for a reason that has nothing to do with the
decompiler.

usage: corpus_names.py <corpus>
Line one is the scored functions, line two the helper callees, space separated.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import verify_rendering as verifier  # noqa: E402


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <corpus>", file=sys.stderr)
        return 64
    corpus = sys.argv[1]
    if corpus not in verifier.CORPUS_SPECS:
        print(
            f"unknown corpus: {corpus} "
            f"(known: {' '.join(sorted(verifier.CORPUS_SPECS))})",
            file=sys.stderr,
        )
        return 65
    print(" ".join(verifier.CORPUS_SPECS[corpus]))
    print(" ".join(verifier.CORPUS_CALLEES[corpus]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
