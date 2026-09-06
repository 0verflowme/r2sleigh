#!/usr/bin/env python3
"""Report what a merge dropped, and what it left with two answerers.

A textual merge on this tree is not evidence that the merge is safe. Three
collisions during one integration were resolved silently by git and only one of
them produced a conflict marker: a predicate implemented independently in two
files and both kept, a binding shadowed by a second binding of the same name,
and a parsed-specification owner built twice under one name. A fourth attempt
silently discarded 747 lines and eleven tests because one side's file was taken
whole.

None of that is visible in `git status`. All of it is visible by comparing the
symbols and tests of the merge result against the union of its two parents,
which is what this does.

    python3 tests/merge_audit.py <ours-ref> <theirs-ref>

Run it after the merge is resolved and before it is committed. It reads the
working tree, so it sees exactly what would be committed.
"""

import re
import subprocess
import sys
from collections import defaultdict

FN = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?(?:unsafe\s+)?(?:extern\s+\"[^\"]*\"\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)")
TEST_ATTR = re.compile(r"^\s*#\[(?:test|tokio::test)\]")


def rust_files(ref):
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", ref],
                         capture_output=True, text=True, check=True).stdout
    return [p for p in out.splitlines() if p.endswith(".rs")]


def read(ref, path):
    if ref is None:
        try:
            with open(path, encoding="utf-8", errors="replace") as handle:
                return handle.read()
        except OSError:
            return ""
    got = subprocess.run(["git", "show", f"{ref}:{path}"],
                         capture_output=True, text=True)
    return got.stdout if got.returncode == 0 else ""


def symbols(ref):
    """Every function name, and where it is defined. `ref=None` is the tree."""
    paths = rust_files(ref) if ref is not None else [
        p for p in subprocess.run(["git", "ls-files"], capture_output=True,
                                  text=True, check=True).stdout.splitlines()
        if p.endswith(".rs")]
    defined = defaultdict(set)
    tests = set()
    for path in paths:
        prev_is_test = False
        for line in read(ref, path).splitlines():
            match = FN.match(line)
            if match:
                defined[match.group(1)].add(path)
                if prev_is_test:
                    tests.add(match.group(1))
            prev_is_test = bool(TEST_ATTR.match(line))
    return defined, tests


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 64
    ours, theirs = sys.argv[1], sys.argv[2]
    base = subprocess.run(["git", "merge-base", ours, theirs],
                          capture_output=True, text=True, check=True).stdout.strip()

    base_defs, base_tests = symbols(base)
    ours_defs, ours_tests = symbols(ours)
    theirs_defs, theirs_tests = symbols(theirs)
    now_defs, now_tests = symbols(None)

    def classify(base_set, ours_set, theirs_set, now_set):
        """Split what is missing after the merge by who dropped it.

        A deletion on one side is not automatically legitimate. A branch that
        rewrites a file wholesale deletes everything the other side added to it,
        and that reads identically to an intended removal. So these are reported
        rather than judged: the first list is unambiguous, the other two need a
        human to say whether the deletion was the point or the accident.
        """
        gone = (ours_set | theirs_set) - now_set
        both_had = sorted(name for name in gone
                          if name in ours_set and name in theirs_set)
        ours_only = sorted(name for name in gone
                           if name in ours_set and name not in theirs_set)
        theirs_only = sorted(name for name in gone
                             if name in theirs_set and name not in ours_set)
        return both_had, ours_only, theirs_only

    failures = 0
    review = 0

    def likely_rename(name, appeared):
        """A name that vanished while a near-neighbour appeared is usually a rename.

        Reporting a rename as a deletion is how a correct report gets dismissed
        as noise: `verify_call_sites_are_single` became
        `verify_call_sites_are_single_per_execution`, the audit said the first
        was gone, and it was read as a regex failure rather than as the truth.
        Prefix containment either way catches the common shapes -- a qualifier
        added or dropped -- without pretending to be a similarity metric.
        """
        for other in appeared:
            if other != name and (other.startswith(name) or name.startswith(other)):
                return other
        return None

    def report(kind, both_had, ours_only, theirs_only, appeared=frozenset()):
        nonlocal failures, review
        if both_had:
            failures += 1
            print(f"DROPPED {len(both_had)} {kind}(s) that BOTH sides had:")
            for name in both_had:
                print(f"  {name}")
        if ours_only:
            review += 1
            print(f"\nREVIEW: {len(ours_only)} {kind}(s) on {ours} that {theirs} "
                  f"does not have, gone after the merge.")
            print(f"  Legitimate only if {theirs} deleted them on purpose rather "
                  f"than by rewriting the file they live in.")
            for name in ours_only[:40]:
                into = likely_rename(name, appeared)
                print(f"  {name}" + (f"   (likely renamed to {into})" if into else ""))
            if len(ours_only) > 40:
                print(f"  ... and {len(ours_only) - 40} more")
        if theirs_only:
            review += 1
            print(f"\nREVIEW: {len(theirs_only)} {kind}(s) on {theirs} that {ours} "
                  f"does not have, gone after the merge.")
            for name in theirs_only[:40]:
                into = likely_rename(name, appeared)
                print(f"  {name}" + (f"   (likely renamed to {into})" if into else ""))
            if len(theirs_only) > 40:
                print(f"  ... and {len(theirs_only) - 40} more")

    appeared_tests = now_tests - (ours_tests | theirs_tests)
    appeared_fns = set(now_defs) - (set(ours_defs) | set(theirs_defs))
    report("test", *classify(base_tests, ours_tests, theirs_tests, now_tests),
           appeared=appeared_tests)
    t_both, t_ours, t_theirs = classify(base_tests, ours_tests, theirs_tests, now_tests)
    seen = set(t_both) | set(t_ours) | set(t_theirs)
    f_both, f_ours, f_theirs = classify(set(base_defs), set(ours_defs),
                                        set(theirs_defs), set(now_defs))
    report("function", [n for n in f_both if n not in seen],
           [n for n in f_ours if n not in seen],
           [n for n in f_theirs if n not in seen],
           appeared=appeared_fns)

    # A name defined in one file on each side and in two files after the merge
    # is the collision that reads as a clean merge and is not one.
    doubled = []
    for name, files in now_defs.items():
        if len(files) < 2:
            continue
        was = max(len(ours_defs.get(name, ())), len(theirs_defs.get(name, ())))
        if len(files) > was:
            doubled.append((name, sorted(files)))
    if doubled:
        failures += 1
        print(f"\nTWO ANSWERERS: {len(doubled)} name(s) gained a definition site:")
        for name, files in sorted(doubled):
            print(f"  {name}")
            for path in files:
                print(f"      {path}")

    print()
    if failures:
        print("merge audit: FAILED -- resolve before committing")
        return 1
    if review:
        print("merge audit: NEEDS REVIEW -- read the lists above before committing")
        return 2
    print(f"merge audit: clean ({len(now_tests)} tests, {len(now_defs)} functions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
