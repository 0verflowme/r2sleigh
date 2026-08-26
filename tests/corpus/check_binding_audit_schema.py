#!/usr/bin/env python3
"""Check Rust-produced binding-journal causes against the corpus schema."""

from __future__ import annotations

import json
import sys
from typing import Any

import verify_rendering as verifier


def validate_oracle(value: Any) -> int:
    if not isinstance(value, list):
        raise verifier.BindingAuditFormatError(
            "binding journal cause oracle must be a JSON array"
        )

    seen: set[str] = set()
    for index, candidate in enumerate(value):
        cause = verifier._validate_binding_journal_cause(candidate)
        kind = cause["kind"]
        if kind in seen:
            raise verifier.BindingAuditFormatError(
                f"binding journal cause oracle repeats kind {kind!r} at index {index}"
            )
        seen.add(kind)

    expected = set(verifier.BINDING_AUDIT_JOURNAL_CAUSE_FIELDS)
    if seen != expected:
        raise verifier.BindingAuditFormatError(
            "binding journal cause oracle kind mismatch: "
            f"missing={sorted(expected - seen)} unexpected={sorted(seen - expected)}"
        )
    return len(seen)


def main() -> int:
    try:
        count = validate_oracle(json.load(sys.stdin))
    except (json.JSONDecodeError, verifier.BindingAuditFormatError) as error:
        print(error, file=sys.stderr)
        return 1
    print(count)
    return 0


if __name__ == "__main__":
    sys.exit(main())
