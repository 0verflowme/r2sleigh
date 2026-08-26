#!/usr/bin/env python3
"""Check Rust-produced binding and effect records against the corpus schema."""

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


def validate_effect_obligations(value: Any) -> dict[str, Any]:
    """Validate one Rust-produced effect ledger against the corpus schema."""
    return verifier._validate_effect_obligations(value)


def validate_schema(value: Any) -> int:
    if isinstance(value, list):
        return validate_oracle(value)
    validate_effect_obligations(value)
    return 1


def main() -> int:
    try:
        count = validate_schema(json.load(sys.stdin))
    except (json.JSONDecodeError, verifier.BindingAuditFormatError) as error:
        print(error, file=sys.stderr)
        return 1
    print(count)
    return 0


if __name__ == "__main__":
    sys.exit(main())
