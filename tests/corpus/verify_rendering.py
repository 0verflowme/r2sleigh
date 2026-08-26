#!/usr/bin/env python3
"""Measure every corpus rendering without letting a missing cell disappear.

The harness deliberately reports three different results:

* raw: the emitted declarations, expressions, and body compiled unchanged under
  a strict warning policy.  Only the radare2 linkage name and mapped image data
  are adapted by the compilation envelope.
* diagnostic: the historical type/dereference repair, with every rewrite
  recorded.  This remains useful for diagnosis but is not emitted-C proof.
* differential: the raw executable when available, otherwise the explicitly
  labelled diagnostic executable, compared with the source-built oracle across
  deterministic boundary and randomized inputs.

Cell discovery never drives the result set.  The nine expected functions are
enumerated first, so every invocation produces exactly nine records and the
six-configuration matrix produces exactly 54.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parent
LEGACY_MESSAGE = b"The quick brown fox jumps over the lazy dog, 0123456789abcdef"
CONFIGS = {
    "x64_O0": "h_x64_O0",
    "x64_O1": "h_x64_O1",
    "x64_O2": "h_x64_O2",
    "arm64_O0": "h_arm64_O0",
    "arm64_O1": "h_arm64_O1",
    "arm64_O2": "h_arm64_O2",
}
STRICT_C_FLAGS = (
    "-std=c11",
    "-Wall",
    "-Wextra",
    "-Wpedantic",
    "-Wconversion",
    "-Wsign-conversion",
    "-Werror",
    "-O0",
)
BINDING_AUDIT_PREFIX = "R2SLEIGH_BINDING_AUDIT__"
BINDING_AUDIT_DOMAINS = ("values", "uses", "writes")
BINDING_AUDIT_JOURNAL_FAILURE_REASONS = {
    "journal_construction_failure",
    "journal_recording_failure",
    "journal_seal_failure",
}
BINDING_AUDIT_FAILURE_REASONS = BINDING_AUDIT_JOURNAL_FAILURE_REASONS | {
    "plan_build_failure",
    "source_pairing_failure",
    "report_failure",
}
BINDING_AUDIT_MAX_COUNT = (1 << 64) - 1
BINDING_AUDIT_JOURNAL_CAUSE_FIELDS = {
    "source_authority": frozenset(),
    "binding_plan_authority": frozenset(),
    "binding_plan_machine_untrusted_artifact_provenance": frozenset(),
    "binding_plan_machine_incomplete_obligation_inventory": frozenset(),
    "binding_plan_machine_missing_graph_value": frozenset({"value_id"}),
    "binding_plan_machine_missing_graph_block": frozenset({"block_id"}),
    "binding_plan_machine_duplicate_block_address": frozenset({"address"}),
    "binding_plan_machine_topology_mismatch": frozenset(),
    "binding_plan_machine_context_mismatch": frozenset(),
    "binding_plan_machine_missing_instruction": frozenset({"instruction_id"}),
    "binding_plan_machine_missing_instruction_disposition": frozenset(
        {"instruction_id"}
    ),
    "binding_plan_machine_missing_use_disposition": frozenset(
        {"instruction_id", "input_index"}
    ),
    "binding_plan_machine_missing_write_disposition": frozenset(
        {"instruction_id"}
    ),
    "binding_plan_machine_missing_output": frozenset({"instruction_id"}),
    "binding_plan_machine_invalid_value_width": frozenset(
        {"value_id", "size_bytes"}
    ),
    "binding_plan_machine_constant_too_wide": frozenset(
        {"value_id", "width_bits"}
    ),
    "binding_plan_machine_wrong_operand_count": frozenset(
        {"instruction_id", "expected_count", "actual_count"}
    ),
    "binding_plan_machine_width_mismatch": frozenset(
        {"instruction_id", "expected_bits", "actual_bits"}
    ),
    **{
        f"binding_plan_machine_invalid_{kind}_width": frozenset(
            {"instruction_id", "from_bits", "to_bits"}
        )
        for kind in (
            "zero_extend",
            "sign_extend",
            "truncate",
            "bit_reinterpret",
            "integer_to_address",
            "address_to_integer",
        )
    },
    "binding_plan_machine_invalid_subpiece": frozenset(
        {"instruction_id", "source_bits", "result_bits", "lsb_bits"}
    ),
    "binding_plan_machine_invalid_child": frozenset(
        {"expression_index", "child_index"}
    ),
    "binding_plan_machine_invalid_expression_type": frozenset(
        {"expression_index"}
    ),
    "binding_plan_machine_duplicate_entity": frozenset({"value_id"}),
    "binding_plan_machine_entity_mismatch": frozenset({"instruction_id"}),
    "binding_plan_machine_obligation_mismatch": frozenset({"instruction_id"}),
    "binding_plan_machine_use_disposition_mismatch": frozenset(
        {"instruction_id", "input_index"}
    ),
    "binding_plan_machine_write_disposition_mismatch": frozenset(
        {"instruction_id"}
    ),
    **{
        f"binding_plan_machine_obligation_source_mismatch_phi_{space}": frozenset(
            {"block_address", "storage_offset", "storage_size"}
        )
        for space in ("ram", "register", "unique", "constant", "unknown")
    },
    "binding_plan_machine_obligation_source_mismatch_phi_custom": frozenset(
        {"block_address", "storage_custom_id", "storage_offset", "storage_size"}
    ),
    "binding_plan_machine_obligation_source_mismatch_op": frozenset(
        {"block_address", "op_ordinal"}
    ),
    "binding_plan_machine_obligation_source_mismatch_native_span": frozenset(
        {"block_address", "instruction_address", "instruction_size"}
    ),
    "binding_plan_machine_unsupported_operation": frozenset({"instruction_id"}),
    "binding_plan_value_topology": frozenset({"index", "value_id"}),
    "binding_plan_disposition_count": frozenset({"expected_count", "actual_count"}),
    "binding_plan_binding_count": frozenset({"expected_count", "actual_count"}),
    "binding_plan_invalid_binding_reference": frozenset(
        {"value_id", "binding_index"}
    ),
    "binding_plan_non_bound_value": frozenset({"value_id"}),
    "binding_plan_certificate_membership": frozenset({"binding_index"}),
    "binding_plan_declaration_width": frozenset({"binding_index"}),
    "binding_plan_invalid_literal_inline": frozenset({"value_id"}),
    "binding_plan_invalid_elision_proof": frozenset({"value_id"}),
    "binding_plan_unexpected_value_disposition": frozenset({"value_id"}),
    "binding_plan_stack_object_count": frozenset({"expected_count", "actual_count"}),
    "binding_plan_unexpected_stack_object_disposition": frozenset({"object_id"}),
    "binding_plan_stack_object_certificate": frozenset(
        {"object_id", "binding_index"}
    ),
    "binding_plan_stack_object_declaration_width": frozenset(
        {"object_id", "binding_index"}
    ),
    "normalization_source_authority": frozenset(),
    "normalization_block_topology": frozenset(),
    "normalization_row_count": frozenset({"block_address"}),
    "normalization_original_instruction": frozenset({"block_address", "op_index"}),
    "normalization_original_coverage": frozenset(),
    "normalization_phi_edge": frozenset({"block_address", "op_index"}),
    "normalization_relocated_initializer": frozenset(
        {"block_address", "op_index"}
    ),
    "normalization_removed_phi": frozenset(),
    "normalization_removed_phi_edge": frozenset(),
    "normalization_invalid_carrier_certificates": frozenset(),
    "too_many_observations": frozenset(),
    "invalid_value": frozenset({"value_id"}),
    "invalid_use": frozenset({"instruction_id", "input_index"}),
    "invalid_write": frozenset({"instruction_id"}),
    "outputless_write": frozenset({"instruction_id"}),
    "invalid_normalized_site": frozenset({"block_id", "op_index"}),
    "missing_normalized_block": frozenset({"address"}),
    "missing_normalized_site_context": frozenset(),
    "invalid_normalized_input": frozenset(
        {"block_id", "op_index", "input_index"}
    ),
    "missing_normalized_output": frozenset({"block_id", "op_index"}),
    "refused_rendered_use": frozenset({"instruction_id", "input_index"}),
    "refused_rendered_write": frozenset({"instruction_id"}),
    "rendered_value_required": frozenset({"value_id"}),
    "exact_use_requires_rendered_occurrence": frozenset(
        {"instruction_id", "input_index"}
    ),
    "exact_write_requires_rendered_occurrence": frozenset({"instruction_id"}),
    "symbol_table_mismatch": frozenset(),
    "unowned_binding_symbol": frozenset({"symbol_index"}),
    "conflicting_value": frozenset({"value_id"}),
    "conflicting_use": frozenset({"instruction_id", "input_index"}),
    "conflicting_write": frozenset({"instruction_id"}),
    "observation_domain_too_large": frozenset({"expected_count"}),
    "observation_capacity_unavailable": frozenset({"expected_count"}),
    "observation_out_of_range": frozenset(
        {"observation_id", "expected_count"}
    ),
    "duplicate_observation": frozenset({"observation_id"}),
}
BINDING_AUDIT_LINE = re.compile(
    rf"^{re.escape(BINDING_AUDIT_PREFIX)}(?P<payload>[^\r\n]*)(?:\r?\n|$)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class FunctionSpec:
    result_bits: int
    arity: int
    default_seed: int = 0

    @property
    def c_result_type(self) -> str:
        return f"uint{self.result_bits}_t"

    @property
    def printf_width(self) -> int:
        return self.result_bits // 4


SPECS: dict[str, FunctionSpec] = {
    "fnv1a32": FunctionSpec(32, 2),
    "fnv1a64": FunctionSpec(64, 2),
    "djb2": FunctionSpec(32, 2),
    "sdbm": FunctionSpec(32, 2),
    "adler32": FunctionSpec(32, 2),
    "crc32_bitwise": FunctionSpec(32, 2),
    "murmur3_32": FunctionSpec(32, 3, 0x9747B28C),
    "xxhash32": FunctionSpec(32, 3, 0),
    "pearson": FunctionSpec(8, 2),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_exact_text(path: Path) -> str:
    with path.open("r", encoding="utf-8", newline="") as stream:
        return stream.read()


def write_exact_text(path: Path, text: str) -> None:
    with path.open("w", encoding="utf-8", newline="") as stream:
        stream.write(text)


def run_command(
    command: list[str], *, cwd: Path | None = None, timeout: float | None = None
) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        return {
            "status": "timeout",
            "command": command,
            "exit_code": None,
            "stdout": error.stdout or "",
            "stderr": error.stderr or "",
        }
    except OSError as error:
        return {
            "status": "infrastructure_error",
            "command": command,
            "exit_code": None,
            "stdout": "",
            "stderr": str(error),
        }
    return {
        "status": "pass" if completed.returncode == 0 else "failed",
        "command": command,
        "exit_code": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }


def marked_sections(text: str) -> dict[str, list[str]]:
    marker = re.compile(
        r"^R2SLEIGH_CORPUS_BEGIN__(?P<name>[A-Za-z0-9_]+)[\t ]*\r?\n"
        r"(?P<body>.*?)"
        r"^R2SLEIGH_CORPUS_END__(?P=name)[\t ]*(?:\r?\n|$)",
        re.MULTILINE | re.DOTALL,
    )
    sections: dict[str, list[str]] = {}
    for match in marker.finditer(text):
        sections.setdefault(match.group("name"), []).append(match.group("body"))
    return sections


class BindingAuditFormatError(ValueError):
    """One binding-audit marker is present but does not match schema version 2."""


def _exact_object(
    value: Any, expected_keys: set[str], *, context: str
) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BindingAuditFormatError(f"{context} must be a JSON object")
    actual_keys = set(value)
    if actual_keys != expected_keys:
        missing = sorted(expected_keys - actual_keys)
        unexpected = sorted(actual_keys - expected_keys)
        raise BindingAuditFormatError(
            f"{context} keys mismatch: missing={missing} unexpected={unexpected}"
        )
    return value


def _count(value: Any, *, context: str) -> int:
    if (
        isinstance(value, bool)
        or not isinstance(value, int)
        or value < 0
        or value > BINDING_AUDIT_MAX_COUNT
    ):
        raise BindingAuditFormatError(f"{context} must be an unsigned 64-bit integer")
    return value


def _audit_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise BindingAuditFormatError(f"duplicate binding audit field: {key}")
        value[key] = item
    return value


def _invalid_json_constant(value: str) -> None:
    raise BindingAuditFormatError(f"invalid binding audit JSON constant: {value}")


def _audit_domains(
    value: Any, fields: tuple[str, ...], *, context: str
) -> dict[str, dict[str, int]]:
    domains = _exact_object(value, set(BINDING_AUDIT_DOMAINS), context=context)
    parsed: dict[str, dict[str, int]] = {}
    for domain in BINDING_AUDIT_DOMAINS:
        counts = _exact_object(
            domains[domain], set(fields), context=f"{context}.{domain}"
        )
        parsed[domain] = {
            field: _count(counts[field], context=f"{context}.{domain}.{field}")
            for field in fields
        }
    return parsed


def _score_counted_binding_audit(
    envelope: dict[str, Any], audit: dict[str, Any]
) -> dict[str, Any]:
    audit = _exact_object(
        audit,
        {"schema_version", "status", "observations", "shadow"},
        context="binding audit",
    )
    if isinstance(audit["schema_version"], bool) or audit["schema_version"] != 2:
        raise BindingAuditFormatError("binding audit schema_version must be 2")
    source_status = audit["status"]
    if source_status not in {
        "complete",
        "incomplete_observations",
        "non_quality",
    }:
        raise BindingAuditFormatError("counted binding audit has an invalid status")

    observations = _audit_domains(
        audit["observations"],
        (
            "total",
            "rendered",
            "justified_elision",
            "refused",
            "unaccounted",
        ),
        context="binding audit observations",
    )
    shadow = _audit_domains(
        audit["shadow"],
        (
            "total",
            "observed",
            "agree_correct",
            "old_wrong",
            "shadow_wrong",
            "both_wrong_equal",
            "both_wrong_different",
            "unclassified",
            "refused",
        ),
        context="binding audit shadow",
    )

    observation_equations = {
        domain: counts["total"]
        == counts["rendered"]
        + counts["justified_elision"]
        + counts["refused"]
        + counts["unaccounted"]
        for domain, counts in observations.items()
    }
    shadow_equations = {
        domain: counts["total"] == counts["observed"]
        and counts["observed"]
        == counts["agree_correct"]
        + counts["old_wrong"]
        + counts["shadow_wrong"]
        + counts["both_wrong_equal"]
        + counts["both_wrong_different"]
        + counts["unclassified"]
        for domain, counts in shadow.items()
    }
    totals_match = {
        domain: observations[domain]["total"] == shadow[domain]["total"]
        for domain in BINDING_AUDIT_DOMAINS
    }
    observation_quality = {
        domain: observation_equations[domain]
        and counts["unaccounted"] == 0
        and counts["refused"] == 0
        for domain, counts in observations.items()
    }
    shadow_quality = {
        domain: shadow_equations[domain]
        and counts["shadow_wrong"] == 0
        and counts["both_wrong_equal"] == 0
        and counts["both_wrong_different"] == 0
        and counts["unclassified"] == 0
        and counts["refused"] == 0
        for domain, counts in shadow.items()
    }
    canonical_total = sum(
        observations[domain]["total"] for domain in BINDING_AUDIT_DOMAINS
    )
    passes = (
        envelope["request_status"] == "completed"
        and source_status == "complete"
        and all(observation_quality.values())
        and all(shadow_quality.values())
        and all(totals_match.values())
        and canonical_total > 0
    )
    return {
        "status": "pass" if passes else "non_quality",
        "request_status": envelope["request_status"],
        "source_status": source_status,
        "marker_count": 1,
        "record": envelope,
        "equations": {
            "observations": observation_equations,
            "shadow": shadow_equations,
            "totals_match": totals_match,
        },
        "quality": {
            "observations": observation_quality,
            "shadow": shadow_quality,
            "canonical_nonempty": canonical_total > 0,
        },
        "canonical_total": canonical_total,
    }


def _validate_binding_journal_cause(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BindingAuditFormatError("binding audit seal cause must be an object")
    kind = value.get("kind")
    if not isinstance(kind, str) or kind not in BINDING_AUDIT_JOURNAL_CAUSE_FIELDS:
        raise BindingAuditFormatError("binding audit seal cause kind is invalid")
    fields = BINDING_AUDIT_JOURNAL_CAUSE_FIELDS[kind]
    cause = _exact_object(
        value,
        {"kind", *fields},
        context="binding audit seal cause",
    )
    for field in fields:
        _count(cause[field], context=f"binding audit seal cause.{field}")
    return cause


def parse_binding_audit(section: str) -> tuple[str, dict[str, Any]]:
    """Remove and score the one exact out-of-band audit line in a section."""
    matches = list(BINDING_AUDIT_LINE.finditer(section))
    cleaned = BINDING_AUDIT_LINE.sub("", section)
    if not matches:
        return cleaned, {"status": "missing", "marker_count": 0}
    if len(matches) != 1:
        return cleaned, {"status": "duplicate", "marker_count": len(matches)}

    payload = matches[0].group("payload")
    try:
        record = json.loads(
            payload,
            object_pairs_hook=_audit_json_object,
            parse_constant=_invalid_json_constant,
        )
        if not isinstance(record, dict):
            raise BindingAuditFormatError("binding audit must be a JSON object")
        if payload != json.dumps(record, separators=(",", ":"), ensure_ascii=False):
            raise BindingAuditFormatError(
                "binding audit JSON must be compact and directly follow the prefix"
            )
        record = _exact_object(
            record,
            {"schema_version", "request_status", "audit"},
            context="binding audit envelope",
        )
        if isinstance(record["schema_version"], bool) or record["schema_version"] != 2:
            raise BindingAuditFormatError(
                "binding audit envelope schema_version must be 2"
            )
        request_status = record["request_status"]
        if request_status not in {"completed", "refused"}:
            raise BindingAuditFormatError(
                "binding audit request_status must be completed or refused"
            )
        audit = record["audit"]
        if not isinstance(audit, dict):
            raise BindingAuditFormatError("binding audit audit must be a JSON object")
        status = audit.get("status")
        if status in {"complete", "incomplete_observations", "non_quality"}:
            return cleaned, _score_counted_binding_audit(record, audit)
        if status == "failed":
            reason = audit.get("reason")
            if reason not in BINDING_AUDIT_FAILURE_REASONS:
                raise BindingAuditFormatError(
                    "failed binding audit reason is not in the schema"
                )
            expected_fields = {"schema_version", "status", "reason"}
            if reason in BINDING_AUDIT_JOURNAL_FAILURE_REASONS:
                expected_fields.add("cause")
            _exact_object(
                audit,
                expected_fields,
                context="failed binding audit",
            )
            if isinstance(audit["schema_version"], bool) or audit["schema_version"] != 2:
                raise BindingAuditFormatError("binding audit schema_version must be 2")
            if reason in BINDING_AUDIT_JOURNAL_FAILURE_REASONS:
                _validate_binding_journal_cause(audit["cause"])
            return cleaned, {
                "status": "failed",
                "request_status": request_status,
                "marker_count": 1,
                "record": record,
            }
        if status == "not_run":
            _exact_object(
                audit,
                {"schema_version", "status"},
                context="not-run binding audit",
            )
            if isinstance(audit["schema_version"], bool) or audit["schema_version"] != 2:
                raise BindingAuditFormatError("binding audit schema_version must be 2")
            return cleaned, {
                "status": "not_run",
                "request_status": request_status,
                "marker_count": 1,
                "record": record,
            }
        raise BindingAuditFormatError(f"unsupported binding audit status: {status!r}")
    except (json.JSONDecodeError, BindingAuditFormatError) as error:
        return cleaned, {
            "status": "malformed",
            "marker_count": 1,
            "error": str(error),
        }


def _matching_brace(text: str, opening: int) -> int | None:
    depth = 0
    state = "code"
    escaped = False
    index = opening
    while index < len(text):
        char = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""
        if state == "line_comment":
            if char == "\n":
                state = "code"
        elif state == "block_comment":
            if char == "*" and following == "/":
                state = "code"
                index += 1
        elif state in {"string", "character"}:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif (state == "string" and char == '"') or (
                state == "character" and char == "'"
            ):
                state = "code"
        elif char == "/" and following == "/":
            state = "line_comment"
            index += 1
        elif char == "/" and following == "*":
            state = "block_comment"
            index += 1
        elif char == '"':
            state = "string"
        elif char == "'":
            state = "character"
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return None


def extract_function(section: str, name: str) -> tuple[str | None, str | None]:
    candidates: list[tuple[int, int]] = []
    for line_match in re.finditer(r"(?m)^.*$", section):
        line = line_match.group(0)
        if re.search(rf"(?:^|[._]){re.escape(name)}\s*\(", line):
            candidates.append((line_match.start(), line_match.end()))
    if len(candidates) != 1:
        return None, f"expected one signature for {name}, found {len(candidates)}"
    start, signature_end = candidates[0]
    opening = section.find("{", signature_end)
    if opening < 0:
        return None, "signature has no function body"
    closing = _matching_brace(section, opening)
    if closing is None:
        return None, "function body has unbalanced braces"
    return section[start : closing + 1].rstrip() + "\n", None


def normalize_linkage_name(source: str, name: str) -> tuple[str, dict[str, Any]]:
    opening = source.find("{")
    signature = source[:opening]
    pattern = re.compile(
        rf"[A-Za-z_][A-Za-z0-9_.$:]*(?:[._]){re.escape(name)}(?=\s*\()"
    )
    normalized_signature, count = pattern.subn(f"dec_{name}", signature, count=1)
    if count == 0:
        fallback = re.compile(rf"\b{re.escape(name)}(?=\s*\()")
        normalized_signature, count = fallback.subn(
            f"dec_{name}", signature, count=1
        )
    return normalized_signature + source[opening:], {
        "kind": "linkage_name",
        "count": count,
        "semantic": False,
    }


def rendered_arity(source: str) -> int | None:
    opening = source.find("(")
    closing = source.find(")", opening + 1)
    if opening < 0 or closing < 0:
        return None
    params = source[opening + 1 : closing].strip()
    if not params or params == "void":
        return 0
    depth = 0
    count = 1
    for char in params:
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "," and depth == 0:
            count += 1
    return count


def diagnostic_repair(source: str, name: str) -> tuple[str, list[dict[str, Any]], int]:
    rewrites: list[dict[str, Any]] = []
    repaired, linkage = normalize_linkage_name(source, name)
    rewrites.append(linkage)

    signature_end = repaired.find(")")
    if signature_end < 0:
        return repaired, rewrites, 0
    signature, rest = repaired[: signature_end + 1], repaired[signature_end + 1 :]
    params = signature[signature.find("(") + 1 : -1].strip()
    parameter_count = rendered_arity(repaired) or 0
    if params and params != "void":
        replacement = ", ".join(f"long arg{index}" for index in range(parameter_count))
        before = signature
        signature = signature[: signature.find("(") + 1] + replacement + ")"
        rewrites.append(
            {
                "kind": "parameter_retype",
                "count": 1,
                "semantic": True,
                "before_sha256": sha256_text(before),
                "after_sha256": sha256_text(signature),
            }
        )

    def rewrite(
        kind: str,
        pattern: str,
        replacement: str | Callable[[re.Match[str]], str],
        text: str,
        *,
        flags: int = 0,
        semantic: bool = True,
    ) -> str:
        changed, count = re.subn(pattern, replacement, text, flags=flags)
        rewrites.append({"kind": kind, "count": count, "semantic": semantic})
        return changed

    signature = rewrite(
        "return_retype", r"^\S+\s+dec_", "long dec_", signature, semantic=True
    )
    rest = rewrite("comment_removal", r"/\*.*?\*/", "", rest, flags=re.DOTALL)
    rest = rewrite(
        "local_retype",
        r"\b(?:u?int(?:8|16|32|64|128|512)_t)\s+(\w+)",
        r"long \1",
        rest,
    )
    rest = rewrite(
        "typed_deref_stash",
        r"\*\s*\(\s*((?:__)?u?int(?:8|16|32|64|128)_t)\s*\*\s*\)\s*",
        r"@@D\1@@",
        rest,
        semantic=False,
    )

    assumed_widths = 0

    def subscript(match: re.Match[str]) -> str:
        nonlocal assumed_widths
        assumed_widths += 1
        return f"(((unsigned char *)(long)({match.group(1)}))[{match.group(2)}])"

    previous = None
    while previous != rest:
        previous = rest
        rest = rewrite(
            "subscript_byte_width",
            r"([A-Za-z_]\w*|0[xX][0-9a-fA-F]+[uU]?)\s*\[([^\[\]]+)\]",
            subscript,
            rest,
        )
        rest = rewrite(
            "parenthesized_subscript_byte_width",
            r"\(([^()\[\]]*)\)\s*\[([^\[\]]+)\]",
            subscript,
            rest,
        )

    def bare_deref(match: re.Match[str]) -> str:
        nonlocal assumed_widths
        assumed_widths += 1
        return f"(*(unsigned char *)(long)({match.group(1)}))"

    rest = rewrite("bare_deref_byte_width", r"\*\(([^()]*)\)", bare_deref, rest)
    rest = rewrite("bare_name_deref_byte_width", r"\*([A-Za-z_]\w*)\b", bare_deref, rest)
    rest = rewrite(
        "typed_deref_restore",
        r"@@D((?:__)?u?int(?:8|16|32|64|128)_t)@@",
        r"*(\1 *)(long)",
        rest,
        semantic=False,
    )
    return signature + rest, rewrites, assumed_widths


def _json_stdout(command: list[str]) -> Any:
    result = run_command(command)
    if result["status"] != "pass":
        raise RuntimeError(result["stderr"] or "command failed")
    output = result["stdout"].strip()
    try:
        return json.loads(output)
    except json.JSONDecodeError:
        for line in reversed(output.splitlines()):
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                continue
    raise RuntimeError(f"command did not return JSON: {' '.join(command)}")


def certified_image_literals(
    source: str, mapped_ranges: list[tuple[int, int]]
) -> list[dict[str, Any]]:
    def containing(address: int) -> tuple[int, int] | None:
        return next(
            ((start, end) for start, end in mapped_ranges if start <= address < end),
            None,
        )

    certified: list[dict[str, Any]] = []
    for match in re.finditer(r"\b0x[0-9a-fA-F]{9,}\b", source):
        address = int(match.group(0), 16)
        if containing(address) is None:
            continue
        prefix = source[max(0, match.start() - 120) : match.start()]
        suffix = source[match.end() : match.end() + 40]
        evidence = []
        if re.search(
            r"\(\s*(?:const\s+)?(?:void|char|(?:__)?u?int(?:8|16|32|64|128)_t)\s*\*\s*\)"
            r"(?:\s*\(\s*(?:u?intptr_t|long)\s*\))?\s*\(?\s*$",
            prefix,
        ):
            evidence.append("explicit_pointer_cast")
        if re.match(r"(?:[uUlL]{0,3})\s*\[", suffix):
            evidence.append("subscript_base")
        if evidence:
            certified.append(
                {
                    "start": match.start(),
                    "end": match.end(),
                    "address": address,
                    "evidence": sorted(set(evidence)),
                }
            )
    return certified


def map_image_data(
    source: str, binary: Path
) -> tuple[str, list[str], list[dict[str, Any]]]:
    sections = _json_stdout(
        ["r2", "-e", "scr.color=0", "-q", "-c", "iSj", str(binary)]
    )
    mapped_ranges: list[tuple[int, int]] = []
    for section in sections:
        start = int(section.get("vaddr", 0))
        size = int(section.get("vsize") or section.get("size") or 0)
        if start and size:
            mapped_ranges.append((start, start + size))

    certified = certified_image_literals(source, mapped_ranges)
    by_address: dict[int, list[dict[str, Any]]] = {}
    for occurrence in certified:
        by_address.setdefault(occurrence["address"], []).append(occurrence)

    blobs: list[str] = []
    records: list[dict[str, Any]] = []
    replacements: dict[int, str] = {}
    for index, address in enumerate(sorted(by_address)):
        containing_range = next(
            ((start, end) for start, end in mapped_ranges if start <= address < end),
            None,
        )
        _, end = containing_range or (address, address)
        length = min(4096, end - address)
        data = _json_stdout(
            [
                "r2",
                "-e",
                "scr.color=0",
                "-q",
                "-c",
                f"s {address}; p8j {length}",
                str(binary),
            ]
        )
        if not isinstance(data, list) or not all(isinstance(byte, int) for byte in data):
            raise RuntimeError(f"invalid p8j payload for 0x{address:x}")
        blob_name = f"corpus_blob_{index}"
        initializer = ",".join(str(byte) for byte in data)
        blobs.append(f"static unsigned char {blob_name}[{len(data)}] = {{{initializer}}};")
        replacements[address] = f"((uintptr_t){blob_name})"
        occurrences = by_address[address]
        records.append(
            {
                "kind": "mapped_image_address",
                "address": address,
                "bytes": len(data),
                "count": len(occurrences),
                "semantic": False,
                "evidence": sorted(
                    {
                        evidence
                        for occurrence in occurrences
                        for evidence in occurrence["evidence"]
                    }
                ),
            }
        )
    mapped = source
    for occurrence in reversed(certified):
        mapped = (
            mapped[: occurrence["start"]]
            + replacements[occurrence["address"]]
            + mapped[occurrence["end"] :]
        )
    return mapped, blobs, records


def cases_for(name: str, spec: FunctionSpec) -> list[dict[str, Any]]:
    lengths = [0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 31, 32, 61]
    cases: list[dict[str, Any]] = []
    for length in lengths:
        if length == len(LEGACY_MESSAGE):
            data = LEGACY_MESSAGE
        else:
            generator = random.Random(0x5232534C ^ length)
            data = bytes(generator.randrange(256) for _ in range(length))
        cases.append(
            {
                "case_id": f"boundary:{length}",
                "bytes": data.hex(),
                "length": length,
                "seed": spec.default_seed,
            }
        )
    for length in [5, 12, 24, 63, 96]:
        generator = random.Random(0xB17D1A6 ^ length)
        data = bytes(generator.randrange(256) for _ in range(length))
        cases.append(
            {
                "case_id": f"random:{length}",
                "bytes": data.hex(),
                "length": length,
                "seed": spec.default_seed,
            }
        )
    if spec.arity == 3:
        seeded_data = bytes((index * 37 + 11) & 0xFF for index in range(17))
        seed_values = dict.fromkeys(
            [0, 1, spec.default_seed, 0xFFFFFFFF, 0x13579BDF]
        )
        for seed in seed_values:
            cases.append(
                {
                    "case_id": f"seed:{seed}",
                    "bytes": seeded_data.hex(),
                    "length": 17,
                    "seed": seed,
                }
            )
    return cases


def runner_source(
    function_source: str,
    blobs: list[str],
    name: str,
    spec: FunctionSpec,
    cases: list[dict[str, Any]],
    *,
    diagnostic: bool,
) -> str:
    arrays = []
    arms = []
    for index, case in enumerate(cases):
        data = bytes.fromhex(case["bytes"])
        initializer = ",".join(str(byte) for byte in data) if data else "0"
        arrays.append(f"static unsigned char case_{index}[] = {{{initializer}}};")
        args = [f"case_{index}", f"{case['length']}u"]
        if spec.arity == 3:
            args.append(f"UINT32_C({case['seed']})")
        if diagnostic:
            args = [f"(long)(uintptr_t){args[0]}", f"(long){args[1]}"] + [
                f"(long){arg}" for arg in args[2:]
            ]
        callee = f"dec_{name}" if diagnostic else "corpus_checked_fn"
        call = f"{callee}({', '.join(args)})"
        arms.append(
            f"case {index}u: printf(\"%0{spec.printf_width}\" PRIx{spec.result_bits} \"\\n\", "
            f"({spec.c_result_type})({call})); return 0;"
        )
    expected_parameters = "const uint8_t *, size_t"
    if spec.arity == 3:
        expected_parameters += ", uint32_t"
    type_check = []
    if not diagnostic:
        type_check = [
            f"typedef {spec.c_result_type} (*corpus_expected_fn)({expected_parameters});",
            f"static corpus_expected_fn corpus_checked_fn = &dec_{name};",
        ]
    return "\n".join(
        [
            "#include <inttypes.h>",
            "#include <stddef.h>",
            "#include <stdint.h>",
            "#include <stdio.h>",
            "#include <stdlib.h>",
            *blobs,
            *arrays,
            function_source,
            *type_check,
            "int main(int argc, char **argv) {",
            f"    if (argc != 2) return {64};",
            "    char *end = NULL;",
            "    unsigned long selected = strtoul(argv[1], &end, 10);",
            "    if (end == argv[1] || *end != '\\0') return 65;",
            "    switch (selected) {",
            *(f"    {arm}" for arm in arms),
            "    default: return 66;",
            "    }",
            "}",
            "",
        ]
    )


def compile_runner(
    source: str, source_path: Path, executable: Path, *, strict: bool
) -> dict[str, Any]:
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(source)
    flags = list(STRICT_C_FLAGS) if strict else ["-std=c11", "-w", "-O0"]
    result = run_command(["clang", *flags, "-o", str(executable), str(source_path)])
    result["source"] = str(source_path)
    result["executable"] = str(executable)
    return result


def run_case(executable: Path, index: int) -> dict[str, Any]:
    result = run_command([str(executable), str(index)], timeout=3)
    if result["status"] == "pass":
        result["value"] = result["stdout"].strip().lower()
    return result


def oracle_case(
    oracle: Path, name: str, spec: FunctionSpec, case: dict[str, Any]
) -> dict[str, Any]:
    payload = case["bytes"] or "-"
    command = [str(oracle), name, payload]
    if spec.arity == 3:
        command.append(str(case["seed"]))
    result = run_command(command, timeout=3)
    if result["status"] == "pass":
        result["value"] = result["stdout"].strip().lower()
    return result


def load_baseline(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text())
    if data.get("schema_version") != 1 or not isinstance(data.get("raw_sha256"), dict):
        raise ValueError(f"unsupported baseline manifest: {path}")
    baseline = {str(key): str(value) for key, value in data["raw_sha256"].items()}
    expected = {
        f"{config}/{function}" for config in CONFIGS for function in SPECS
    }
    if set(baseline) != expected:
        missing = sorted(expected - set(baseline))
        unexpected = sorted(set(baseline) - expected)
        raise ValueError(
            f"baseline key mismatch: missing={missing} unexpected={unexpected}"
        )
    malformed = sorted(
        key
        for key, value in baseline.items()
        if re.fullmatch(r"[0-9a-f]{64}", value) is None
    )
    if malformed:
        raise ValueError(f"baseline has malformed SHA-256 values: {malformed}")
    return baseline


def first_error(result: dict[str, Any]) -> str:
    for line in str(result.get("stderr", "")).splitlines():
        if "error:" in line:
            return line.strip()
    return str(result.get("status", "unknown"))


def verify(args: argparse.Namespace) -> dict[str, Any]:
    output_text = read_exact_text(args.input)
    sections = marked_sections(output_text)
    artifact_root: Path = args.artifact_root
    raw_dir = artifact_root / "raw"
    compile_dir = artifact_root / "compile" / args.config
    raw_dir.mkdir(parents=True, exist_ok=True)
    compile_dir.mkdir(parents=True, exist_ok=True)
    baseline = load_baseline(args.baseline)
    entries: list[dict[str, Any]] = []

    for name, spec in SPECS.items():
        key = f"{args.config}/{name}"
        entry: dict[str, Any] = {
            "config": args.config,
            "function": name,
            "generation": {"status": "missing", "section_count": 0},
            "raw": {"status": "not_run"},
            "diagnostic": {"status": "not_run"},
            "differential": {"status": "not_run", "cases": []},
            "snapshot": {"status": "missing"},
            "binding_audit": {"status": "missing", "marker_count": 0},
        }
        found = sections.get(name, [])
        entry["generation"]["section_count"] = len(found)
        if len(found) != 1:
            entry["generation"]["status"] = "missing" if not found else "duplicate"
            entries.append(entry)
            continue
        exact_section, entry["binding_audit"] = parse_binding_audit(found[0])
        section_dir = artifact_root / "raw-sections"
        section_dir.mkdir(parents=True, exist_ok=True)
        section_path = section_dir / f"{args.config}_{name}.txt"
        write_exact_text(section_path, exact_section)
        section_hash = sha256_text(exact_section)
        entry["generation"].update(
            {
                "section_path": str(section_path),
                "section_sha256": section_hash,
            }
        )
        expected_hash = baseline.get(key)
        entry["snapshot"] = {
            "status": "missing"
            if expected_hash is None
            else ("match" if expected_hash == section_hash else "mismatch"),
            "expected_sha256": expected_hash,
            "actual_sha256": section_hash,
        }
        raw_source, extraction_error = extract_function(exact_section, name)
        if extraction_error or raw_source is None:
            terminal_status = (
                "renderer_error"
                if exact_section.lstrip().startswith("ERROR:")
                else "unparsable"
            )
            terminal_error = (
                exact_section.strip()
                if terminal_status == "renderer_error"
                else extraction_error
            )
            entry["generation"].update(
                {"status": terminal_status, "error": terminal_error}
            )
            entry["raw"] = {"status": "blocked_generation"}
            entry["diagnostic"] = {"status": "blocked_generation", "rewrites": []}
            entry["differential"] = {
                "status": "blocked_generation",
                "basis": None,
                "cases": [],
            }
            entries.append(entry)
            continue

        raw_path = raw_dir / f"{args.config}_{name}.c"
        raw_path.write_text(raw_source)
        raw_hash = sha256_text(raw_source)
        entry["generation"].update(
            {
                "status": "present",
                "raw_path": str(raw_path),
                "raw_sha256": raw_hash,
            }
        )

        normalized, linkage_rewrite = normalize_linkage_name(raw_source, name)
        arity = rendered_arity(normalized)
        entry["generation"]["rendered_arity"] = arity
        entry["generation"]["expected_arity"] = spec.arity
        cases = cases_for(name, spec)

        if arity != spec.arity or linkage_rewrite["count"] != 1:
            entry["raw"] = {
                "status": "signature_mismatch",
                "linkage_rewrite": linkage_rewrite,
            }
            entry["diagnostic"] = {"status": "signature_mismatch", "rewrites": []}
            entry["differential"] = {
                "status": "blocked_signature",
                "basis": None,
                "cases": [],
            }
            entries.append(entry)
            continue

        try:
            raw_mapped, raw_blobs, raw_mapping = map_image_data(normalized, args.binary)
        except (RuntimeError, ValueError) as error:
            entry["raw"] = {"status": "infrastructure_error", "error": str(error)}
            entries.append(entry)
            continue

        raw_program = runner_source(
            raw_mapped, raw_blobs, name, spec, cases, diagnostic=False
        )
        raw_compile = compile_runner(
            raw_program,
            compile_dir / f"raw_{name}.c",
            compile_dir / f"raw_{name}",
            strict=True,
        )
        raw_compile["linkage_rewrite"] = linkage_rewrite
        raw_compile["data_mapping"] = raw_mapping
        entry["raw"] = raw_compile

        diagnostic_source, rewrites, assumed_widths = diagnostic_repair(raw_source, name)
        diagnostic_compile: dict[str, Any]
        try:
            diagnostic_mapped, diagnostic_blobs, diagnostic_mapping = map_image_data(
                diagnostic_source, args.binary
            )
            rewrites.extend(diagnostic_mapping)
            diagnostic_program = runner_source(
                diagnostic_mapped,
                diagnostic_blobs,
                name,
                spec,
                cases,
                diagnostic=True,
            )
            diagnostic_compile = compile_runner(
                diagnostic_program,
                compile_dir / f"diagnostic_{name}.c",
                compile_dir / f"diagnostic_{name}",
                strict=False,
            )
        except (RuntimeError, ValueError) as error:
            diagnostic_compile = {
                "status": "infrastructure_error",
                "error": str(error),
            }
        diagnostic_compile["rewrites"] = rewrites
        diagnostic_compile["assumed_widths"] = assumed_widths
        entry["diagnostic"] = diagnostic_compile

        legacy_index = next(
            index
            for index, case in enumerate(cases)
            if case["length"] == len(LEGACY_MESSAGE) and case["seed"] == spec.default_seed
        )
        oracle_legacy = oracle_case(args.oracle, name, spec, cases[legacy_index])
        if oracle_legacy["status"] != "pass":
            diagnostic_compile["status"] = "infrastructure_error"
            diagnostic_compile["oracle"] = oracle_legacy
        elif diagnostic_compile["status"] == "pass":
            diagnostic_run = run_case(Path(diagnostic_compile["executable"]), legacy_index)
            diagnostic_compile["run"] = diagnostic_run
            diagnostic_compile["oracle"] = oracle_legacy
            if diagnostic_run.get("value") != oracle_legacy.get("value"):
                diagnostic_compile["status"] = "wrong"

        basis: str | None = None
        executable: Path | None = None
        if raw_compile["status"] == "pass":
            basis = "raw"
            executable = Path(raw_compile["executable"])
        elif diagnostic_compile["status"] in {"pass", "wrong"} and Path(
            diagnostic_compile["executable"]
        ).exists():
            basis = "diagnostic"
            executable = Path(diagnostic_compile["executable"])

        differential_cases: list[dict[str, Any]] = []
        differential_status = "blocked_compile" if executable is None else "pass"
        if executable is not None:
            for index, case in enumerate(cases):
                expected = oracle_case(args.oracle, name, spec, case)
                actual = run_case(executable, index)
                case_status = "pass"
                if expected["status"] != "pass":
                    case_status = "oracle_error"
                elif actual["status"] != "pass":
                    case_status = actual["status"]
                elif actual.get("value") != expected.get("value"):
                    case_status = "wrong"
                if case_status != "pass":
                    differential_status = "failed"
                differential_cases.append(
                    {
                        **case,
                        "status": case_status,
                        "expected": expected.get("value"),
                        "actual": actual.get("value"),
                        "oracle_exit": expected.get("exit_code"),
                        "rendered_exit": actual.get("exit_code"),
                        "rendered_stderr": actual.get("stderr", ""),
                    }
                )
        entry["differential"] = {
            "status": differential_status,
            "basis": basis,
            "cases": differential_cases,
        }
        entries.append(entry)

    return {
        "schema_version": 1,
        "config": args.config,
        "expected_entries": len(SPECS),
        "input": str(args.input),
        "binary": str(args.binary),
        "oracle": str(args.oracle),
        "strict_c_flags": list(STRICT_C_FLAGS),
        "entries": entries,
    }


def print_summary(report: dict[str, Any]) -> None:
    print(f"== {report['config']} ({len(report['entries'])}/{report['expected_entries']} cells)")
    for entry in report["entries"]:
        print(
            f"  {entry['function']:<15}"
            f"gen={entry['generation']['status']:<10} "
            f"raw={entry['raw']['status']:<18} "
            f"diag={entry['diagnostic']['status']:<18} "
            f"diff={entry['differential']['status']:<16} "
            f"basis={str(entry['differential'].get('basis')):<10} "
            f"snapshot={entry['snapshot']['status']:<10} "
            f"binding_audit={entry['binding_audit']['status']}"
        )
        if entry["raw"].get("status") == "failed":
            print(f"    raw: {first_error(entry['raw'])}")
        if entry["diagnostic"].get("status") in {"failed", "wrong"}:
            print(f"    diagnostic: {first_error(entry['diagnostic'])}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("config", choices=tuple(CONFIGS))
    parser.add_argument("--input", type=Path)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--oracle", type=Path)
    parser.add_argument("--artifact-root", type=Path, default=ROOT / "artifacts")
    parser.add_argument(
        "--baseline", type=Path, default=ROOT / "raw-baseline-sha256.json"
    )
    args = parser.parse_args()
    args.input = args.input or args.artifact_root / "dumps" / f"out_{args.config}.txt"
    args.binary = args.binary or args.artifact_root / "bin" / CONFIGS[args.config]
    args.oracle = args.oracle or args.artifact_root / "bin" / f"oracle_{args.config}"
    for label in ("input", "binary", "oracle"):
        path = getattr(args, label)
        if not path.exists():
            parser.error(f"{label} does not exist: {path}")
    return args


def main() -> int:
    args = parse_args()
    report = verify(args)
    result_dir = args.artifact_root / "results"
    result_dir.mkdir(parents=True, exist_ok=True)
    result_path = result_dir / f"{args.config}.json"
    result_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print_summary(report)
    print(f"  report={result_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
