#!/usr/bin/env python3
"""Score recovery and soundness against a debug build of the same binary.

The same source compiled twice gives exact ground truth for free: the build
that kept its debug info says what every function really is, and the stripped
build is what the plugin has to work from. Every fact the plugin recovers from
the stripped build lands in one of four buckets.

    correct          recovered and it matches the debug build
    missing          the debug build has it and the plugin does not
    marked-wrong     recovered wrongly, but the function carries a residual
                     marker, so a reader was told not to trust it
    silently-wrong   recovered wrongly and asserted as if proven

Recovery is how much of the truth comes back. Soundness is the share of
asserted facts that are not silently wrong, and it is the number that matters:
a decompiler that guesses confidently is worse than one that says it does not
know. Silently-wrong is a defect at the highest severity, never a quality nit.

The marker granularity is the function, because that is the granularity the
renderer annotates at. A function carrying any residual has its unmatched facts
counted as marked rather than silent.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

PROTOTYPE = re.compile(r"^(?P<ret>[\w \*]+?)\s+(?P<name>[\w.]+)\s*\((?P<args>.*)\);?\s*$")


def r2(binary: Path, commands: str, r2_bin: str, plugin: bool) -> str:
    prelude = "a:sla > /dev/null\n" if plugin else ""
    proc = subprocess.run(
        [r2_bin, "-e", "scr.color=false", "-e", "log.level=0",
         "-e", "bin.relocs.apply=true", "-Qc", prelude + commands, str(binary)],
        capture_output=True, text=True, timeout=1800,
    )
    return proc.stdout


@dataclass
class Prototype:
    ret: str
    params: list[str] = field(default_factory=list)


def normalize_type(spelling: str) -> str:
    """Compare what a type means, not how it is spelled.

    `char *` and `char*` are the same type, and a debug build that says
    `unsigned long` against a plugin that says `size_t` is a naming difference
    rather than a recovery failure.
    """
    text = " ".join(spelling.split()).replace(" *", "*").strip()
    aliases = {
        "unsigned long": "size_t", "long unsigned int": "size_t",
        "unsigned int": "uint32_t", "int32_t": "int", "signed int": "int",
        "int64_t": "long", "uint64_t": "size_t", "_Bool": "bool",
    }
    return aliases.get(text, text)


def parse_prototype(line: str) -> Prototype | None:
    match = PROTOTYPE.match(line.strip())
    if not match:
        return None
    args = match.group("args").strip()
    params: list[str] = []
    if args and args != "void":
        for arg in args.split(","):
            # `char *s` gives its type by dropping the trailing identifier.
            tokens = arg.strip().rsplit(" ", 1)
            params.append(normalize_type(tokens[0] if len(tokens) > 1 else arg))
    return Prototype(normalize_type(match.group("ret")), params)


GENERIC_PARAM = re.compile(r"^(int64_t|int32_t|uint64_t|long|int)$")


def truth_is_real(truth: dict[int, Prototype]) -> bool:
    """Refuse a debug build whose prototypes are radare2's own guesses.

    Debug info that fails to load looks exactly like debug info that says
    nothing: every function comes back `void f(int64_t arg1)`. Scoring against
    that measures the plugin against a guess and reports the difference as the
    plugin's error, which is worse than reporting nothing. A real debug build
    names concrete types a generic recovery never produces.
    """
    if not truth:
        return False
    concrete = sum(
        1 for proto in truth.values()
        if proto.ret not in {"void", "int"}
        or any("*" in param or not GENERIC_PARAM.match(param) for param in proto.params)
    )
    return concrete * 4 >= len(truth)


def truth_from_debug_build(binary: Path, r2_bin: str) -> dict[int, Prototype]:
    """What every function actually is, read out of the debug build."""
    out = r2(binary, "aaa\nafl~[0]", r2_bin, plugin=False)
    truth: dict[int, Prototype] = {}
    for addr_text in out.split():
        try:
            addr = int(addr_text, 16)
        except ValueError:
            continue
        signature = r2(binary, f"aaa\ns {addr}\nafs", r2_bin, plugin=False).strip().splitlines()
        if not signature:
            continue
        proto = parse_prototype(signature[-1])
        if proto:
            truth[addr] = proto
    return truth


def recovered_from_stripped(binary: Path, r2_bin: str) -> dict[int, tuple[Prototype, bool]]:
    """What the plugin recovers, and whether it marked the function."""
    out = r2(binary, "aaa\nafl~[0]", r2_bin, plugin=True)
    recovered: dict[int, tuple[Prototype, bool]] = {}
    for addr_text in out.split():
        try:
            addr = int(addr_text, 16)
        except ValueError:
            continue
        body = r2(binary, f"aaa\ns {addr}\npdd", r2_bin, plugin=True)
        lines = [line for line in body.splitlines() if line.strip()]
        if not lines:
            continue
        proto = parse_prototype(lines[0])
        if proto:
            recovered[addr] = (proto, "residual" in body)
    return recovered


def score(truth: dict[int, Prototype],
          recovered: dict[int, tuple[Prototype, bool]]) -> dict[str, int]:
    buckets = {"correct": 0, "missing": 0, "marked_wrong": 0, "silently_wrong": 0}

    def judge(expected: str, actual: str | None, marked: bool) -> None:
        if actual is None:
            buckets["missing"] += 1
        elif actual == expected:
            buckets["correct"] += 1
        elif marked:
            buckets["marked_wrong"] += 1
        else:
            buckets["silently_wrong"] += 1

    for addr, expected in truth.items():
        entry = recovered.get(addr)
        if entry is None:
            buckets["missing"] += 1 + len(expected.params)
            continue
        actual, marked = entry
        judge(expected.ret, actual.ret, marked)
        for index, param in enumerate(expected.params):
            got = actual.params[index] if index < len(actual.params) else None
            judge(param, got, marked)
    return buckets


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--debug-build", type=Path, required=True,
                        help="build that kept its debug info; the ground truth")
    parser.add_argument("--stripped-build", type=Path, required=True,
                        help="same source, stripped; what the plugin is given")
    parser.add_argument("--radare2", default="radare2")
    parser.add_argument("--json", type=Path, help="write the report here")
    args = parser.parse_args()

    truth = truth_from_debug_build(args.debug_build, args.radare2)
    if not truth_is_real(truth):
        print("refusing to score: the debug build yields generic prototypes, so its "
              "debug info did not load. Check that the dSYM or DWARF sits where "
              "radare2 looks for it; a copied binary usually leaves it behind.",
              file=sys.stderr)
        return 2
    recovered = recovered_from_stripped(args.stripped_build, args.radare2)
    buckets = score(truth, recovered)

    asserted = buckets["correct"] + buckets["silently_wrong"]
    facts = sum(buckets.values())
    report = {
        "functions_in_truth": len(truth),
        "functions_recovered": len(recovered),
        "facts": buckets,
        "recovery_rate": round(buckets["correct"] / facts, 4) if facts else 0.0,
        "soundness_rate": round(1 - buckets["silently_wrong"] / asserted, 4) if asserted else 1.0,
    }
    print(json.dumps(report, indent=2))
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    # A silent error is the one failure this harness exists to catch.
    return 1 if buckets["silently_wrong"] else 0


if __name__ == "__main__":
    sys.exit(main())
