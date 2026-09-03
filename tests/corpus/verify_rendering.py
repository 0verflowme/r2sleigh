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
BITVECTOR_PRELUDE = (
    ROOT.parents[1] / "crates" / "r2dec" / "include" / "r2sleigh_bitvectors.h"
).read_text()
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
BINDING_AUDIT_PLACEMENT_FAILURE_REASONS = {"placement_refusal"}
BINDING_AUDIT_FAILURE_REASONS = (
    BINDING_AUDIT_JOURNAL_FAILURE_REASONS
    | BINDING_AUDIT_PLACEMENT_FAILURE_REASONS
    | {
        "plan_build_failure",
        "source_pairing_failure",
        "report_failure",
    }
)
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
    "binding_plan_parameter_count": frozenset(
        {"expected_count", "actual_count"}
    ),
    "binding_plan_unexpected_parameter_disposition": frozenset(
        {"parameter_slot"}
    ),
    "binding_plan_parameter_certificate": frozenset(
        {"parameter_slot", "binding_index"}
    ),
    "binding_plan_parameter_declaration_width": frozenset(
        {"parameter_slot", "binding_index"}
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
    "invalid_certified_value_read": frozenset(
        {"value_id", "instruction_id"}
    ),
    "invalid_use": frozenset({"instruction_id", "input_index"}),
    "invalid_write": frozenset({"instruction_id"}),
    "invalid_effect_obligation": frozenset({"obligation"}),
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
    "planned_elided_value_rendered": frozenset({"value_id"}),
    "planned_refused_value_rendered": frozenset({"value_id"}),
    "missing_planned_value": frozenset({"value_id"}),
    "invalid_planned_inline": frozenset({"value_id", "expression_index"}),
    "exact_use_requires_rendered_occurrence": frozenset(
        {"instruction_id", "input_index"}
    ),
    "exact_write_requires_rendered_occurrence": frozenset({"instruction_id"}),
    "symbol_table_mismatch": frozenset(),
    "unowned_binding_symbol": frozenset({"value_id", "symbol_index"}),
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
PLACEMENT_AUDIT_CAUSE_FIELDS = {
    "missing_structured_region_artifact": frozenset(),
    "observation_journal_unavailable": frozenset(),
    "source_authority_mismatch": frozenset(),
    "binding_outside_plan": frozenset({"binding_index"}),
    "region_outside_artifact": frozenset({"region_index"}),
    "block_outside_function": frozenset({"block_address"}),
    "region_does_not_dominate_occurrence": frozenset(
        {"region_index", "block_address"}
    ),
    "external_binding_outside_plan": frozenset({"binding_index"}),
    "region_marker_unsealed": frozenset(),
    "region_marker_foreign": frozenset({"anchor_index"}),
    "region_marker_duplicate": frozenset({"region_index"}),
    "region_marker_missing": frozenset({"region_index"}),
    "region_marker_parent_mismatch": frozenset({"region_index"}),
    "region_marker_out_of_order": frozenset(
        {"region_index", "expected_region_index"}
    ),
    "observation_domain_too_large": frozenset({"expected_count"}),
    "observation_capacity_unavailable": frozenset({"expected_count"}),
    "observation_out_of_range": frozenset(
        {"observation_id", "expected_count"}
    ),
    "duplicate_observation": frozenset({"observation_id"}),
    "missing_observation_target": frozenset({"observation_id"}),
    "invalid_use": frozenset({"instruction_id", "input_index"}),
    "invalid_write": frozenset({"instruction_id"}),
    "invalid_certified_value_read": frozenset(
        {"value_id", "instruction_id"}
    ),
    "missing_planned_value": frozenset({"value_id"}),
    "refused_planned_value": frozenset({"value_id"}),
    "unscoped_observation": frozenset({"observation_id"}),
    "unauthorized_program_variable": frozenset({"symbol_index"}),
    "unobserved_binding_read": frozenset({"binding_index"}),
    "unobserved_binding_write": frozenset({"binding_index"}),
    "no_dominating_region": frozenset({"binding_index"}),
    "missing_definition": frozenset({"binding_index"}),
    "read_before_assignment": frozenset(
        {"binding_index", "instruction_id", "input_index"}
    ),
    "certified_value_read_before_assignment": frozenset(
        {"binding_index", "value_id", "instruction_id"}
    ),
    "stack_access_read_before_assignment": frozenset(
        {"binding_index", "instruction_id", "access_ordinal"}
    ),
    "preserved_carrier_read_before_assignment": frozenset(
        {"binding_index", "instruction_id"}
    ),
    "unprovable_execution_order": frozenset({"binding_index"}),
    "ambiguous_observation_execution_order": frozenset({"observation_id"}),
    "missing_binding": frozenset({"binding_index"}),
    "missing_binding_symbol": frozenset({"binding_index"}),
    "external_binding_missing_parameter": frozenset({"binding_index"}),
    "missing_region": frozenset({"region_index"}),
    "duplicate_region": frozenset({"region_index"}),
    "missing_inline_write": frozenset({"instruction_id"}),
    "duplicate_inline_write": frozenset({"instruction_id"}),
    "missing_binding_role": frozenset({"binding_index"}),
    "undeclared_names": frozenset({"count"}),
}
RENDER_REFUSAL_KINDS = {
    "incomplete_effect_inventory",
    "missing_machine_projection_authorization",
    "missing_program_variable_authorization",
    "normalization_origin_unavailable",
    "unrepresentable_control_flow",
    "unrepresentable_operation",
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


@dataclass(frozen=True)
class ScalarSpec:
    """A function the corpus calls with plain integers rather than a buffer.

    `FunctionSpec` describes the one shape the hash corpus has: a byte buffer,
    a length, and optionally a seed. Nothing outside that shape can be
    expressed by it, which is why the semantic gate saw only hash functions.
    This is the second description: N unsigned 64-bit arguments in, one
    unsigned integer out, with the argument vectors named here so a function
    that needs particular operands -- a negative dividend, say -- gets them.

    The interesting shape lives inside the function and in the helpers it
    calls, not in its interface, so the harness needs to know nothing about
    structs, frames or recursion in order to score them.
    """

    result_bits: int
    arity: int
    arguments: tuple[tuple[int, ...], ...]

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

# One argument vector set for every shape. The values are chosen so that the
# operands reach the cases a shape can get wrong: zero and one for the
# degenerate paths, values whose signed reading is negative for the division
# shape, INT64_MIN over minus one for the quotient that has no representation,
# and two full-width mixed patterns so a truncation to 32 bits shows.
SHAPE_ARGUMENTS: tuple[tuple[int, ...], ...] = (
    (0x0, 0x0),
    (0x0, 0x1),
    (0x1, 0x0),
    (0x1, 0x1),
    (0x2, 0x3),
    (0xC, 0x5),
    (0xFF, 0x100),
    (0x7FFFFFFF, 0x80000000),
    (0xFFFFFFFFFFFFFFFF, 0x1),
    (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
    (0x8000000000000000, 0xFFFFFFFFFFFFFFFF),
    (0xFFFFFFFFFFFFFFF9, 0x7),
    (0x7, 0xFFFFFFFFFFFFFFFD),
    (0xDEADBEEFCAFEBABE, 0x0123456789ABCDEF),
    (0x0123456789ABCDEF, 0xFEDCBA9876543210),
    (0x9E3779B97F4A7C15, 0xC2B2AE3D27D4EB4F),
)

SHAPE_SPECS: dict[str, ScalarSpec] = {
    name: ScalarSpec(64, 2, SHAPE_ARGUMENTS)
    for name in (
        "shape_variadic",
        "shape_variadic_local",
        "shape_call_chain",
        "shape_struct_pointer",
        "shape_struct_value",
        "shape_struct_array",
        "shape_stack_buffer",
        "shape_recurse_direct",
        "shape_recurse_mutual",
        "shape_signed_divmod",
        "shape_multiword_return",
        "shape_pointer_to_pointer",
        "shape_function_pointer",
    )
}

# Leaf functions, deliberately. The shape corpus asks whether a program shape
# renders at all and mostly gets a refusal at a call boundary or a frame object.
# These have neither, so the renderer has nothing to decline on and must commit
# to an answer; the hazard is in the arithmetic, where a wrong result is a
# plausible number rather than a refusal.
VALUE_SPECS: dict[str, ScalarSpec] = {
    name: ScalarSpec(64, 2, SHAPE_ARGUMENTS)
    for name in (
        "value_sign_extend",
        "value_arith_shift",
        "value_signed_compare",
        "value_narrow_wrap",
        "value_div_pow2",
        "value_rotate",
        "value_carry_chain",
        "value_mul_high",
        "value_byte_order",
        "value_count_bits",
        "value_overflow_flags",
        "value_abs_minmax",
        "value_width_conflict",
    )
}

# The helpers each corpus carries. They are not scored, but a rendered call
# needs its callee defined in the same translation unit, so the sweep captures
# them under their own marker and `callee_definitions` picks them up by name.
# The value corpus has none on purpose: a helper would reintroduce the call
# boundary those functions exist to avoid.
CORPUS_CALLEES = {
    "hashes": ("rotl32",),
    "shapes": (
        "vfold",
        "shape_step",
        "shape_stash",
        "mixed_touch",
        "mixed_fold",
        "shape_mutual_even",
        "shape_mutual_odd",
        "wide_make",
        "indirect_load",
        "indirect_store",
        "op_add",
        "op_xor",
        "op_mul",
    ),
    "values": (),
}

CORPUS_SPECS: dict[str, dict[str, Any]] = {
    "hashes": SPECS,
    "shapes": SHAPE_SPECS,
    "values": VALUE_SPECS,
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
    """One audit sidecar is present but does not match its exact schema."""


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
        source_status == "complete"
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


def _score_observation_only_binding_audit(
    envelope: dict[str, Any], audit: dict[str, Any]
) -> dict[str, Any]:
    audit = _exact_object(
        audit,
        {"schema_version", "status", "observations"},
        context="observation-only binding audit",
    )
    if isinstance(audit["schema_version"], bool) or audit["schema_version"] != 2:
        raise BindingAuditFormatError("binding audit schema_version must be 2")
    if audit["status"] != "non_quality_observations":
        raise BindingAuditFormatError("observation-only binding audit status is invalid")
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
    equations = {
        domain: counts["total"]
        == counts["rendered"]
        + counts["justified_elision"]
        + counts["refused"]
        + counts["unaccounted"]
        for domain, counts in observations.items()
    }
    quality = {
        domain: equations[domain]
        and counts["refused"] == 0
        and counts["unaccounted"] == 0
        for domain, counts in observations.items()
    }
    return {
        "status": "non_quality",
        "request_status": envelope["request_status"],
        "source_status": audit["status"],
        "marker_count": 1,
        "record": envelope,
        "equations": {"observations": equations},
        "quality": {"observations": quality},
        "canonical_total": sum(
            observations[domain]["total"] for domain in BINDING_AUDIT_DOMAINS
        ),
    }


def _validate_effect_obligations(value: Any) -> dict[str, Any]:
    effect = _exact_object(
        value,
        {
            "schema_version",
            "status",
            "total",
            "rendered",
            "justified_elision",
            "refused",
            "unaccounted",
            "conflicts",
        },
        context="effect obligations",
    )
    if isinstance(effect["schema_version"], bool) or effect["schema_version"] != 1:
        raise BindingAuditFormatError("effect obligations schema_version must be 1")
    if effect["status"] not in {"admitted", "refused", "not_run"}:
        raise BindingAuditFormatError("effect obligations status is invalid")
    for field in (
        "total",
        "rendered",
        "justified_elision",
        "refused",
        "unaccounted",
        "conflicts",
    ):
        _count(effect[field], context=f"effect obligations.{field}")
    return effect


def _score_effect_obligations(envelope: dict[str, Any]) -> dict[str, Any]:
    effect = _validate_effect_obligations(envelope["effect_obligations"])
    equation_balanced = effect["total"] == (
        effect["rendered"]
        + effect["justified_elision"]
        + effect["refused"]
        + effect["unaccounted"]
    )
    quality = {
        "admitted": effect["status"] == "admitted",
        "equation_balanced": equation_balanced,
        "zero_refused": effect["refused"] == 0,
        "zero_unaccounted": effect["unaccounted"] == 0,
        "zero_conflicts": effect["conflicts"] == 0,
    }
    if effect["status"] == "refused":
        score_status = "refused"
    elif effect["status"] == "not_run":
        score_status = "not_run"
    else:
        score_status = "pass" if all(quality.values()) else "non_quality"
    return {
        "status": score_status,
        "request_status": envelope["request_status"],
        "source_status": effect["status"],
        "marker_count": 1,
        "record": effect,
        "equation_balanced": equation_balanced,
        "quality": quality,
    }


def _validate_placement_cause(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BindingAuditFormatError("placement audit cause must be an object")
    kind = value.get("kind")
    if not isinstance(kind, str) or kind not in PLACEMENT_AUDIT_CAUSE_FIELDS:
        raise BindingAuditFormatError("placement audit cause kind is invalid")
    fields = PLACEMENT_AUDIT_CAUSE_FIELDS[kind]
    cause = _exact_object(
        value,
        {"kind", *fields},
        context="placement audit cause",
    )
    for field in fields:
        _count(cause[field], context=f"placement audit cause.{field}")
    return cause


def _score_placement_audit(envelope: dict[str, Any]) -> dict[str, Any]:
    placement = envelope["placement_audit"]
    if not isinstance(placement, dict):
        raise BindingAuditFormatError("placement audit must be an object")
    status = placement.get("status")
    expected_fields = {"schema_version", "status", "cause"} if status == "refused" else {
        "schema_version",
        "status",
    }
    placement = _exact_object(
        placement,
        expected_fields,
        context="placement audit",
    )
    if isinstance(placement["schema_version"], bool) or placement["schema_version"] != 1:
        raise BindingAuditFormatError("placement audit schema_version must be 1")
    if status not in {"applied", "refused", "not_run"}:
        raise BindingAuditFormatError("placement audit status is invalid")
    if status == "refused":
        _validate_placement_cause(placement["cause"])
    return {
        "status": "pass" if status == "applied" else status,
        "request_status": envelope["request_status"],
        "source_status": status,
        "marker_count": 1,
        "record": placement,
    }


def _validate_canonical_storage(value: Any, *, context: str) -> dict[str, Any]:
    storage = _exact_object(
        value,
        {"space", "offset", "size"},
        context=context,
    )
    space = storage["space"]
    if isinstance(space, str):
        if space not in {"Ram", "Register", "Unique", "Constant", "Unknown"}:
            raise BindingAuditFormatError(f"{context}.space is invalid")
    else:
        custom = _exact_object(space, {"Custom"}, context=f"{context}.space")
        _count(custom["Custom"], context=f"{context}.space.Custom")
    _count(storage["offset"], context=f"{context}.offset")
    _count(storage["size"], context=f"{context}.size")
    return storage


def _validate_semantic_obligation(value: Any, *, context: str) -> dict[str, Any]:
    obligation = _exact_object(
        value,
        {"instruction", "kind", "component"},
        context=context,
    )
    instruction = _exact_object(
        obligation["instruction"],
        {"block_addr", "site"},
        context=f"{context}.instruction",
    )
    _count(instruction["block_addr"], context=f"{context}.instruction.block_addr")
    site = instruction["site"]
    if not isinstance(site, dict) or len(site) != 1:
        raise BindingAuditFormatError(f"{context}.instruction.site is invalid")
    site_kind, site_value = next(iter(site.items()))
    if site_kind == "Phi":
        _validate_canonical_storage(site_value, context=f"{context}.instruction.site.Phi")
    elif site_kind == "Op":
        _count(site_value, context=f"{context}.instruction.site.Op")
    elif site_kind == "NativeSpan":
        native = _exact_object(
            site_value,
            {"instruction_addr", "size"},
            context=f"{context}.instruction.site.NativeSpan",
        )
        _count(
            native["instruction_addr"],
            context=f"{context}.instruction.site.NativeSpan.instruction_addr",
        )
        _count(native["size"], context=f"{context}.instruction.site.NativeSpan.size")
    else:
        raise BindingAuditFormatError(f"{context}.instruction.site is invalid")

    if obligation["kind"] not in {
        "ObservableMemoryRead",
        "ObservableMemoryWrite",
        "Call",
        "CallArgument",
        "CallResult",
        "Return",
        "ReturnValue",
        "ControlPredicate",
        "ControlTransfer",
        "Trap",
        "Atomicity",
        "MemoryOrdering",
        "VolatileOrUnknownEffect",
        "LoopCarriedState",
        "LiveStateTransition",
        "LiveValueProducer",
    }:
        raise BindingAuditFormatError(f"{context}.kind is invalid")

    component = obligation["component"]
    if isinstance(component, str):
        if component not in {"Whole", "PredicateOperand"}:
            raise BindingAuditFormatError(f"{context}.component is invalid")
        return obligation
    if not isinstance(component, dict) or len(component) != 1:
        raise BindingAuditFormatError(f"{context}.component is invalid")
    component_kind, component_value = next(iter(component.items()))
    if component_kind in {"MemoryAccess", "Index"}:
        _count(component_value, context=f"{context}.component.{component_kind}")
    elif component_kind == "RegisterSlot":
        slot = _exact_object(
            component_value,
            {"index", "storage"},
            context=f"{context}.component.RegisterSlot",
        )
        _count(slot["index"], context=f"{context}.component.RegisterSlot.index")
        _validate_canonical_storage(
            slot["storage"], context=f"{context}.component.RegisterSlot.storage"
        )
    elif component_kind == "StackOffset":
        if (
            isinstance(component_value, bool)
            or not isinstance(component_value, int)
            or component_value < -(1 << 63)
            or component_value >= (1 << 63)
        ):
            raise BindingAuditFormatError(
                f"{context}.component.StackOffset must be a signed 64-bit integer"
            )
    elif component_kind == "LoopTransition":
        transition = _exact_object(
            component_value,
            {"carrier", "predecessor"},
            context=f"{context}.component.LoopTransition",
        )
        _validate_canonical_storage(
            transition["carrier"],
            context=f"{context}.component.LoopTransition.carrier",
        )
        _count(
            transition["predecessor"],
            context=f"{context}.component.LoopTransition.predecessor",
        )
    elif component_kind == "MemoryOrdering":
        if component_value not in {
            "Relaxed",
            "Acquire",
            "Release",
            "AcqRel",
            "SeqCst",
            "Unknown",
        }:
            raise BindingAuditFormatError(
                f"{context}.component.MemoryOrdering is invalid"
            )
    else:
        raise BindingAuditFormatError(f"{context}.component is invalid")
    return obligation


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
        if field == "obligation":
            _validate_semantic_obligation(
                cause[field], context="binding audit seal cause.obligation"
            )
        else:
            _count(cause[field], context=f"binding audit seal cause.{field}")
    return cause


def _score_binding_audit(envelope: dict[str, Any]) -> dict[str, Any]:
    request_status = envelope["request_status"]
    audit = envelope["audit"]
    if not isinstance(audit, dict):
        raise BindingAuditFormatError("binding audit audit must be a JSON object")
    status = audit.get("status")
    if status in {"complete", "incomplete_observations", "non_quality"}:
        return _score_counted_binding_audit(envelope, audit)
    if status == "non_quality_observations":
        return _score_observation_only_binding_audit(envelope, audit)
    if status == "failed":
        reason = audit.get("reason")
        if reason not in BINDING_AUDIT_FAILURE_REASONS:
            raise BindingAuditFormatError(
                "failed binding audit reason is not in the schema"
            )
        expected_fields = {"schema_version", "status", "reason"}
        if reason in (
            BINDING_AUDIT_JOURNAL_FAILURE_REASONS
            | BINDING_AUDIT_PLACEMENT_FAILURE_REASONS
        ):
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
        elif reason in BINDING_AUDIT_PLACEMENT_FAILURE_REASONS:
            _validate_placement_cause(audit["cause"])
        return {
            "status": "failed",
            "request_status": request_status,
            "marker_count": 1,
            "record": envelope,
        }
    if status == "not_run":
        _exact_object(
            audit,
            {"schema_version", "status"},
            context="not-run binding audit",
        )
        if isinstance(audit["schema_version"], bool) or audit["schema_version"] != 2:
            raise BindingAuditFormatError("binding audit schema_version must be 2")
        return {
            "status": "not_run",
            "request_status": request_status,
            "marker_count": 1,
            "record": envelope,
        }
    raise BindingAuditFormatError(f"unsupported binding audit status: {status!r}")


# Machine detail that survives into the emitted C.
#
# Each predicate below is exact rather than a threshold: the rendering either
# spells a piece of the machine that the program does not contain, or it does
# not.  A condition-code carrier, a self-assignment, a temporary that holds
# only a literal, and a cast that converts a type to itself are all artifacts
# of rendering one machine operation per C statement; none of them can be
# justified by a source construct, so the honest target for every one of them
# is zero.  They are reported for every cell from the moment the column exists
# and gated separately (`--gate noise`), so the count is visible while the
# rewriting layer is built and becomes a wall once it is finished.
_TYPE_WORD = (
    r"(?:u?int(?:8|16|32|64|128)_t|__u?int128_t|_Bool|void|char|short|int|long"
    r"|float|double|unsigned|signed|const|struct|[A-Za-z_]\w*_t)"
)
CAST_PATTERN = rf"\(\s*{_TYPE_WORD}(?:\s+{_TYPE_WORD})*\s*(?:\*\s*)*\)"
CAST_RE = re.compile(CAST_PATTERN)
CAST_RUN_RE = re.compile(rf"(?:{CAST_PATTERN}\s*){{2,}}")
FLAG_CARRIER_RE = re.compile(r"\b(?:TMP)?(?:ZF|CF|OF|SF|PF|AF|ZR|CY|OV|NG|NZ)_\d+\b")
SELF_ASSIGN_RE = re.compile(
    rf"^\s*([A-Za-z_]\w*)\s*=\s*(?:{CAST_PATTERN}\s*)*\1\s*;", re.MULTILINE
)
# A name this renderer minted for a machine value: a lowered temporary, or an
# SSA-versioned machine register.  A program-derived name (`total`) and a named
# frame slot (`stack_m40`) are locals the source could have written, so a
# literal initialiser on one of those is ordinary C and not machine detail.
MINTED_CARRIER = r"(?:tmp_\w+|[A-Z][A-Z0-9]*_\d+)"
LITERAL_ONLY_DECL_RE = re.compile(
    rf"^\s*{_TYPE_WORD}(?:\s+{_TYPE_WORD})*\s*\**\s*{MINTED_CARRIER}\s*=\s*"
    rf"(?:{CAST_PATTERN}\s*)*-?\s*(?:0[xX][0-9a-fA-F]+|\d+)[uUlL]*\s*;",
    re.MULTILINE,
)
CONDITION_KEYWORD_RE = re.compile(r"\b(?:if|while|switch)\s*\(")
UNOPTIMIZED_CONFIGS = frozenset({"x64_O0", "arm64_O0"})


def normalize_cast(text: str) -> str:
    """Spell one cast so two spellings of one type compare equal."""
    inner = re.sub(r"\s+", " ", text.strip()[1:-1]).strip()
    return re.sub(r"\s*\*", "*", inner)


def cast_runs(source: str) -> list[list[str]]:
    """Every maximal run of directly adjacent casts, normalized."""
    return [
        [normalize_cast(cast.group(0)) for cast in CAST_RE.finditer(run.group(0))]
        for run in CAST_RUN_RE.finditer(source)
    ]


DECLARATION_RE = re.compile(
    rf"^\s*({_TYPE_WORD}(?:\s+{_TYPE_WORD})*\s*(?:\*\s*)*)\s*([A-Za-z_]\w*)\s*(?:=|;|,|\))",
    re.MULTILINE,
)
PARAMETER_RE = re.compile(
    rf"({_TYPE_WORD}(?:\s+{_TYPE_WORD})*\s*(?:\*\s*)*)\s*([A-Za-z_]\w*)\s*(?=,|\))"
)
CAST_OF_NAME_RE = re.compile(rf"({CAST_PATTERN})\s*([A-Za-z_]\w*)\b(?!\s*\()")


def declared_types(source: str) -> dict[str, str]:
    """Every name the function declares, with its normalized type.

    Locals come from declarations in the body; parameters from the signature.
    A name declared twice with two types is dropped, because a cast to either
    is then not provably redundant.
    """
    types: dict[str, str] = {}
    ambiguous: set[str] = set()
    signature_end = source.find("{")
    head = source[:signature_end] if signature_end > 0 else ""
    open_paren = head.find("(")
    parameters = head[open_paren + 1 :] if open_paren >= 0 else ""
    for pattern, text in ((PARAMETER_RE, parameters), (DECLARATION_RE, source)):
        for match in pattern.finditer(text):
            ty = normalize_cast("(" + match.group(1) + ")")
            name = match.group(2)
            if name in types and types[name] != ty:
                ambiguous.add(name)
            types.setdefault(name, ty)
    for name in ambiguous:
        types.pop(name, None)
    return types


def casts_to_declared_type(source: str) -> int:
    """Casts that convert a name to the type that name is declared with.

    A run of adjacent identical casts is one shape of redundancy; this is the
    other, and the more common one: `(uint64_t)RAX_2` where `RAX_2` is
    declared `uint64_t`. The pair-based count never examined a lone cast, so
    the column read zero while thousands of these were in the rendered C.
    """
    types = declared_types(source)
    return sum(
        1
        for match in CAST_OF_NAME_RE.finditer(source)
        if types.get(match.group(2)) == normalize_cast(match.group(1))
    )


def parenthesized_conditions(source: str) -> list[str]:
    """The text inside each `if`/`while`/`switch` control parenthesis."""
    conditions: list[str] = []
    for keyword in CONDITION_KEYWORD_RE.finditer(source):
        opening = source.index("(", keyword.start())
        depth = 0
        for index in range(opening, len(source)):
            character = source[index]
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth == 0:
                    conditions.append(source[opening + 1 : index])
                    break
    return conditions


ADDRESS_WIDTH_TYPES = frozenset({"uint64_t", "uintptr_t", "uint32_t", "size_t"})


def cast_is_pointer(cast: str) -> bool:
    return cast.endswith("*")


def run_is_required(run: list[str]) -> bool:
    """Whether a run of adjacent conversions is as short as C allows.

    One or two are always accepted; the pairs that are genuinely required are
    covered in the comment at the call site. Three are accepted only as the
    pointer-carrying shape: an address-width integer with the pointer outside
    it, which is a narrowing carried at the address width and then made a
    pointer. Anything longer, and any three whose innermost conversion is the
    pointer, is a run a shorter one could replace.
    """
    if len(run) <= 2:
        return True
    if len(run) != 3:
        return False
    outermost, middle, innermost = run
    return (
        cast_is_pointer(outermost)
        and middle in ADDRESS_WIDTH_TYPES
        and not cast_is_pointer(innermost)
    )


def _score_machine_noise(source: str, config: str) -> dict[str, Any]:
    runs = cast_runs(source)
    # Two shapes of a cast that converts nothing: an identical cast directly
    # inside another, and a cast to the type its operand is already declared
    # with. The first count alone reported zero while the second stood at
    # thousands, because a lone cast was never examined.
    same_type_cast = sum(
        1
        for run in runs
        for first, second in zip(run, run[1:])
        if first == second
    ) + casts_to_declared_type(source)
    counts = {
        "flag_carriers": len(set(FLAG_CARRIER_RE.findall(source))),
        "self_assignments": len(SELF_ASSIGN_RE.findall(source)),
        "literal_only_declarations": len(LITERAL_ONLY_DECL_RE.findall(source)),
        "same_type_casts": same_type_cast,
        # A run of adjacent conversions is machine detail when a shorter run
        # says the same thing.  Two are often required: a pointer takes the
        # address-width step on its way to a smaller integer, and
        # `(uint64_t)(uint32_t)x` truncates and then widens, which is how a
        # sub-register read reaches the C.
        #
        # Three was assumed to have no such reading and that was wrong.
        # `(uint8_t *)(uint64_t)(uint8_t)e` narrows the value, carries it at
        # the address width, and makes it a pointer, and every step of that
        # does something C cannot skip.  What the shape has in common with the
        # legitimate pairs is the address-width step in the middle with the
        # pointer outside it, so that is what is allowed rather than a bare
        # length.  A run whose innermost conversion is the pointer is not this
        # shape: converting a pointer to the type it already has is redundant
        # however long the run around it.
        "cast_chains": sum(1 for run in runs if not run_is_required(run)),
        "comma_conditions": sum(
            1
            for condition in parenthesized_conditions(source)
            if len(split_top_level_commas(condition)) > 1
        ),
        "gotos": len(re.findall(r"\bgoto\b", source)),
    }
    # Structured control is only claimed for unoptimized builds today; an
    # optimized body may still linearize, so its `goto` count is reported and
    # not required to be zero.
    required = set(counts) if config in UNOPTIMIZED_CONFIGS else set(counts) - {"gotos"}
    failing = sorted(name for name in required if counts[name])
    return {
        "status": "pass" if not failing else "non_quality",
        "counts": counts,
        "failing": failing,
        "gated": sorted(required),
    }


def _score_render_refusal(envelope: dict[str, Any]) -> dict[str, Any]:
    refusal = envelope["render_refusal"]
    if not isinstance(refusal, dict):
        raise BindingAuditFormatError("render refusal must be an object")
    status = refusal.get("status")
    if status == "none":
        _exact_object(
            refusal,
            {"schema_version", "status"},
            context="render refusal",
        )
    elif status == "refused":
        kind = refusal.get("kind")
        if kind == "refused_binding_disposition":
            refusal = _exact_object(
                refusal,
                {"schema_version", "status", "kind", "observations"},
                context="binding-disposition render refusal",
            )
            _audit_domains(
                refusal["observations"],
                (
                    "total",
                    "rendered",
                    "justified_elision",
                    "refused",
                    "unaccounted",
                ),
                context="render refusal observations",
            )
        elif kind in PLACEMENT_AUDIT_CAUSE_FIELDS:
            refusal = _exact_object(
                refusal,
                {"schema_version", "status", "kind", "cause"},
                context="placement render refusal",
            )
            cause = _validate_placement_cause(refusal["cause"])
            if cause["kind"] != kind:
                raise BindingAuditFormatError(
                    "placement render refusal kind disagrees with its cause"
                )
        elif kind in BINDING_AUDIT_JOURNAL_CAUSE_FIELDS:
            refusal = _exact_object(
                refusal,
                {"schema_version", "status", "kind", "cause"},
                context="observation-journal render refusal",
            )
            cause = _validate_binding_journal_cause(refusal["cause"])
            if cause["kind"] != kind:
                raise BindingAuditFormatError(
                    "observation-journal render refusal kind disagrees with its cause"
                )
        elif kind in RENDER_REFUSAL_KINDS:
            _exact_object(
                refusal,
                {"schema_version", "status", "kind"},
                context="render refusal",
            )
        else:
            raise BindingAuditFormatError("render refusal kind is invalid")
    else:
        raise BindingAuditFormatError("render refusal status is invalid")
    if isinstance(refusal["schema_version"], bool) or refusal["schema_version"] != 1:
        raise BindingAuditFormatError("render refusal schema_version must be 1")
    request_status = envelope["request_status"]
    scored_status = (
        "refused"
        if status == "refused"
        else "pass"
        if request_status == "completed"
        else "non_quality"
    )
    return {
        "status": scored_status,
        "source_status": status,
        "request_status": request_status,
        "marker_count": 1,
        "record": envelope,
    }


def parse_render_audits(
    section: str,
) -> tuple[str, dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Remove and independently score binding, effect, placement, and render audits."""
    matches = list(BINDING_AUDIT_LINE.finditer(section))
    cleaned = BINDING_AUDIT_LINE.sub("", section)
    if not matches:
        missing = {"status": "missing", "marker_count": 0}
        return cleaned, missing.copy(), missing.copy(), missing.copy(), missing
    if len(matches) != 1:
        duplicate = {"status": "duplicate", "marker_count": len(matches)}
        return cleaned, duplicate.copy(), duplicate.copy(), duplicate.copy(), duplicate

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
            {
                "schema_version",
                "request_status",
                "audit",
                "effect_obligations",
                "placement_audit",
                "render_refusal",
            },
            context="binding audit envelope",
        )
        if isinstance(record["schema_version"], bool) or record["schema_version"] != 5:
            raise BindingAuditFormatError(
                "binding audit envelope schema_version must be 5"
            )
        request_status = record["request_status"]
        if request_status not in {"completed", "refused"}:
            raise BindingAuditFormatError(
                "binding audit request_status must be completed or refused"
            )
    except (json.JSONDecodeError, BindingAuditFormatError) as error:
        malformed = {
            "status": "malformed",
            "marker_count": 1,
            "error": str(error),
        }
        return cleaned, malformed.copy(), malformed.copy(), malformed.copy(), malformed

    try:
        binding_score = _score_binding_audit(record)
    except BindingAuditFormatError as error:
        binding_score = {
            "status": "malformed",
            "marker_count": 1,
            "error": str(error),
        }
    try:
        effect_score = _score_effect_obligations(record)
    except BindingAuditFormatError as error:
        effect_score = {
            "status": "malformed",
            "marker_count": 1,
            "error": str(error),
        }
    try:
        placement_score = _score_placement_audit(record)
    except BindingAuditFormatError as error:
        placement_score = {
            "status": "malformed",
            "marker_count": 1,
            "error": str(error),
        }
    try:
        render_score = _score_render_refusal(record)
    except BindingAuditFormatError as error:
        render_score = {
            "status": "malformed",
            "marker_count": 1,
            "error": str(error),
        }
    return cleaned, binding_score, effect_score, placement_score, render_score


def parse_binding_audit(section: str) -> tuple[str, dict[str, Any]]:
    """Compatibility entry point returning only the binding side of the sidecar."""
    cleaned, binding_score, _, _, _ = parse_render_audits(section)
    return cleaned, binding_score


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


# The renderer, when it declines, emits one comment in place of the function and
# names why. Reading it is the difference between a cell that says "unparsable"
# and a cell that says which rule refused, which is the whole value of the gate
# on a corpus where most cells refuse.
FALLBACK_REASON_RE = re.compile(
    r"/\* r2dec fallback: skipped decompilation for (?P<function>\S+) "
    r"\((?P<reason>.*?)\) \*/"
)


def fallback_reason(section: str) -> str | None:
    match = FALLBACK_REASON_RE.search(section)
    return match.group("reason") if match else None


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


CALLEE_PROTOTYPE = re.compile(
    r"^\s*[A-Za-z_][A-Za-z0-9_ *]*\s+(?P<name>sym__[A-Za-z0-9_]+)\s*\([^)]*\)\s*;",
    re.MULTILINE,
)


def declared_callees(source: str) -> list[str]:
    """The functions this rendering declares and therefore calls.

    The decompiler emits a block-scope prototype for each callee, so the
    rendering says which definitions the translation unit still needs. Reading
    them from the text keeps the harness from having to know the call graph.
    """
    seen: list[str] = []
    for match in CALLEE_PROTOTYPE.finditer(source):
        name = match.group("name")
        if name not in seen:
            seen.append(name)
    return seen


def callee_definitions(
    sections: dict[str, list[str]], source: str, *, root: str | None = None
) -> tuple[list[str], list[dict[str, Any]]]:
    """Renderings of the callees, for the same translation unit.

    A call needs its callee defined, and the only honest definition is the one
    this decompiler produced: linking the original would prove the caller
    correct given a correct callee, which is a weaker claim than the one this
    corpus makes. A callee with no section is left out -- at -O1 and above these
    helpers are inlined and have no symbol -- and the caller then fails to link,
    which is the truth about that rendering.

    The closure is transitive. A helper that calls a second helper needs that
    one too, and mutual recursion between two helpers needs both; taking only
    the scored function's direct callees left the translation unit short of a
    definition for reasons that had nothing to do with the rendering. `root` is
    the scored function's own name, excluded so a recursive call does not ask
    for a second definition of the function already in the unit.
    """
    definitions: list[str] = []
    notes: list[dict[str, Any]] = []
    resolved: set[str] = {root} if root is not None else set()
    pending = [
        spelled.removeprefix("sym__") for spelled in declared_callees(source)
    ]
    while pending:
        bare = pending.pop(0)
        if bare in resolved:
            continue
        resolved.add(bare)
        found = sections.get(bare, [])
        if len(found) != 1:
            notes.append(
                {
                    "callee": bare,
                    "status": "absent" if not found else "duplicate",
                }
            )
            continue
        section = parse_render_audits(found[0])[0]
        body, error = extract_function(section, bare)
        if body is None:
            notes.append({"callee": bare, "status": "unparsable", "detail": error})
            continue
        definitions.append(body)
        notes.append({"callee": bare, "status": "rendered"})
        pending.extend(
            spelled.removeprefix("sym__") for spelled in declared_callees(body)
        )
    return definitions, notes


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


def rendered_parameter_types(source: str) -> list[str] | None:
    """The parameter types the rendering itself declares.

    The raw score calls the emitted function through the signature the
    decompiler wrote, because `mint_recovered_interface` documents that a
    parameter is an unsigned integer of the register's own width and that
    signedness, pointer-ness and names are never asserted. Requiring the
    emitted signature to equal the source's own types tested a claim the
    decompiler declines to make; that comparison is reported separately as the
    typed-recovery score instead of gating whether the C compiles and runs.
    """
    opening = source.find("(")
    closing = source.find(")", opening + 1)
    if opening < 0 or closing < 0:
        return None
    params = source[opening + 1 : closing].strip()
    if not params or params == "void":
        return []
    fields: list[str] = []
    depth = 0
    current = ""
    for char in params:
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        if char == "," and depth == 0:
            fields.append(current)
            current = ""
        else:
            current += char
    fields.append(current)
    types: list[str] = []
    for field in fields:
        field = field.strip()
        if not field:
            return None
        # Strip the declarator name, keeping any pointer stars with the type.
        match = re.match(r"^(.*?)([A-Za-z_][A-Za-z0-9_]*)$", field)
        declared = (match.group(1) if match else field).strip()
        types.append(declared or field)
    return types


def rendered_return_type(source: str, name: str) -> str | None:
    """The return type the rendering itself declares."""
    opening = source.find("(")
    if opening < 0:
        return None
    signature = source[:opening]
    marker = signature.rfind(f"dec_{name}")
    if marker < 0:
        return None
    return signature[:marker].strip() or None


def rendered_parameter_names(source: str) -> list[str] | None:
    """The parameter names the rendering itself declares."""
    opening = source.find("(")
    closing = source.find(")", opening + 1)
    if opening < 0 or closing < 0:
        return None
    params = source[opening + 1 : closing].strip()
    if not params or params == "void":
        return []
    names: list[str] = []
    depth = 0
    current = ""
    for char in params:
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        if char == "," and depth == 0:
            names.append(current)
            current = ""
        else:
            current += char
    names.append(current)
    declared: list[str] = []
    for field in names:
        match = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*$", field.strip())
        if not match:
            return None
        declared.append(match.group(1))
    return declared


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
        # Retype the parameters, keep their names. The body refers to each
        # parameter by the name the rendering declared, so renaming them
        # positionally left every use undeclared. The diagnostic path widens
        # types on purpose; it must not rename anything.
        declared_names = rendered_parameter_names(repaired)
        if declared_names is not None and len(declared_names) == parameter_count:
            # Widen the integers and leave the pointers alone. Retyping every
            # parameter to `long` was safe while the decompiler declared them
            # all as unsigned machine words; a recovered pointer parameter
            # retyped to `long` makes the body's own `p = (int8_t *)p` an
            # assignment of a pointer to an integer, which is the harness
            # breaking the program it is checking rather than the decompiler
            # emitting a bad one.
            declared_types = [
                part.strip() for part in split_top_level_commas(params)
            ]
            replacement = ", ".join(
                declaration
                if index < len(declared_types) and "*" in declared_types[index]
                else f"long {declared}"
                for index, (declared, declaration) in enumerate(
                    zip(declared_names, declared_types + [""] * parameter_count)
                )
            )
        else:
            replacement = ", ".join(
                f"long arg{index}" for index in range(parameter_count)
            )
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
    # Not a function declaration. The diagnostic pass widens local variables to
    # `long` on purpose, and a callee prototype looks like one: retyping its
    # return gave `long sym__rotl32(...)` against a definition returning
    # `uint64_t`, which is a hard `conflicting types` error rather than the
    # widened-but-compiling program this gate exists to produce.
    rest = rewrite(
        "local_retype",
        r"\b(?:u?int(?:8|16|32|64|128|512)_t)\s+(?=(\w+))\1(?!\s*\()",
        r"long \1",
        rest,
    )
    # A dereference of a pointer-declared local carries no cast, because the
    # declaration already says the type. The rewrites below all key on the
    # `*(T *)x` form the rendering used while every object was a machine word,
    # so the cast is put back before they run and the diagnostic pass keeps
    # seeing the shape it was written for.
    for pointee, pointer_name in re.findall(
        r"\b((?:__)?u?int(?:8|16|32|64|128)_t)\s*\*\s*(\w+)\s*[;=]", rest
    ):
        rest = rewrite(
            "plain_deref_retype",
            rf"(?<=[=(,;{{])(\s*)\*\s*{re.escape(pointer_name)}\b",
            rf"\1*({pointee} *){pointer_name}",
            rest,
            semantic=False,
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
        # An address the machine loads into a register before indexing it
        # reaches its dereference through a variable, so neither adjacency test
        # above sees it. The binding is still an image pointer: the literal
        # lies inside a mapped section, it initializes a name, and that name
        # reaches a dereference in the same rendering. All three are required,
        # and the evidence is recorded under its own kind so the mapping stays
        # auditable rather than widening the two syntactic rules.
        # The conversion is optional. It was required here because every
        # rendering used to spell one, and the renderer now states a type only
        # where the type changes, so `X8_5 = (uint64_t)0x100001000;` became
        # `X8_5 = 0x100001000;` -- the same binding of the same image address
        # to the same name. Keying the evidence on the cast made a rendering
        # that says less look like an unmapped address, and the differential
        # scored the decompiler wrong for the harness's own recognition rule.
        # That is the second time this test has had to stop reading a spelling
        # as the fact it carries.
        assignment = re.search(
            r"\b([A-Za-z_]\w*)\s*=\s*"
            r"(?:\(\s*(?:__)?u?int(?:8|16|32|64|128)_t\s*\)\s*)?$",
            prefix,
        )
        if assignment and re.match(r"(?:[uUlL]{0,3})\s*;", suffix):
            target = re.escape(assignment.group(1))
            # A dereference is `*(uint8_t *)p` while the rendering spells its
            # pointers as machine words, and plain `*p` once the decompiler
            # declares the object a pointer and has no cast left to write. Both
            # are the same evidence -- a name this literal reaches is read
            # through -- and recognising only the first made a better rendering
            # look like an unmapped address and read the wrong bytes.
            dereference = r"\*\s*(?:\([^()]*\*\s*\)|\w)"
            if re.search(rf"{dereference}[^;]*\b{target}\b", source) or re.search(
                rf"\b{target}\b[^;]*?;[\s\S]{{0,4000}}?{dereference}", source
            ):
                evidence.append("pointer_valued_assignment")
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


def split_top_level_commas(text: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    current = ""
    for character in text:
        if character in "([":
            depth += 1
        elif character in ")]":
            depth -= 1
        if character == "," and depth == 0:
            parts.append(current)
            current = ""
            continue
        current += character
    if current.strip():
        parts.append(current)
    return parts


def map_image_data(
    source: str, binary: Path
) -> tuple[str, list[str], list[dict[str, Any]]]:
    # Segments as well as sections. A base the compiler materializes at higher
    # optimization levels is frequently the image base itself, which is inside
    # the `__TEXT` segment but before the first section in it, so a
    # section-only view called it unmapped and left the literal alone. The
    # emitted C then dereferenced a raw absolute address and died, which the
    # differential score reported as the decompiler producing a wrong answer.
    mapped = _json_stdout(["r2", "-e", "scr.color=0", "-q", "-c", "iSj", str(binary)])
    mapped += _json_stdout(["r2", "-e", "scr.color=0", "-q", "-c", "iSSj", str(binary)])
    mapped_ranges: list[tuple[int, int]] = []
    for section in mapped:
        start = int(section.get("vaddr", 0))
        size = int(section.get("vsize") or section.get("size") or 0)
        if start and size:
            mapped_ranges.append((start, start + size))

    certified = certified_image_literals(source, mapped_ranges)
    by_address: dict[int, list[dict[str, Any]]] = {}
    for occurrence in certified:
        by_address.setdefault(occurrence["address"], []).append(occurrence)

    # A named object the decompiler recovered carries the address it stands for
    # on its declaration. The name is what a reader wants; the address is what
    # this has to resolve, and defining the object from the same captured bytes
    # keeps the program runnable without turning the name back into a number.
    named_objects: dict[str, int] = {}
    for name, address in re.findall(
        r"#define (\w+)__r2sleigh_addr 0x([0-9a-f]+)ULL", source
    ):
        named_objects[name] = int(address, 16)
        by_address.setdefault(int(address, 16), [])

    blobs: list[str] = []
    records: list[dict[str, Any]] = []
    replacements: dict[int, str] = {}
    for index, address in enumerate(sorted(by_address)):
        # Follow contiguous mapping past the end of the one section that
        # happens to contain the address. A base loaded with `adrp` is a page
        # address, and what it indexes is frequently in the next section along:
        # pearson's table sits at base + 0xe6c while the containing section ends
        # 3680 bytes in, so a blob cut at that boundary made the emitted C read
        # off the end of its own capture. That is the verifier miscompiling the
        # program it is checking, not the decompiler.
        end = next(
            (end for start, end in mapped_ranges if start <= address < end),
            address,
        )
        for start, candidate_end in sorted(mapped_ranges):
            if start <= end < candidate_end:
                end = candidate_end
        length = min(65536, end - address)
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
        for object_name, object_address in named_objects.items():
            if object_address == address:
                blobs.append(f"#define {object_name} (*(char (*)[]){blob_name})")
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
    # The declaration goes once the object is defined from the capture; leaving
    # it beside the definition makes the compiler expand the definition inside
    # the declaration. Done after the offset rewrites above, which index into
    # the text as the decompiler emitted it.
    if named_objects:
        mapped = re.sub(r"#define \w+__r2sleigh_addr 0x[0-9a-f]+ULL\n", "", mapped)
        mapped = re.sub(r"[ \t]*extern char \w+\[\];[ \t]*\n", "", mapped)
    return mapped, blobs, records


def cases_for(name: str, spec: FunctionSpec | ScalarSpec) -> list[dict[str, Any]]:
    if isinstance(spec, ScalarSpec):
        return [
            {
                "case_id": "args:" + ",".join(f"0x{value:x}" for value in arguments),
                "arguments": list(arguments),
            }
            for arguments in spec.arguments
        ]
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


def scalar_case_arguments(
    case: dict[str, Any],
    *,
    diagnostic: bool,
    declared_parameters: list[str] | None,
) -> list[str]:
    """The call arguments for one scalar case.

    A scalar corpus hands the function integers, so none of the pointer
    conversion the buffer corpus needs applies. Each value is written at its
    full width and converted to whatever type the rendering declared for that
    position: a rendering that recovered a narrower parameter than the source
    has therefore truncates the operand, which is exactly what the machine
    would do and is a difference the differential is entitled to see.
    """
    literals = [f"UINT64_C({value})" for value in case["arguments"]]
    if diagnostic:
        return [f"(unsigned long long){literal}" for literal in literals]
    if declared_parameters is None:
        return literals
    converted = [
        f"({declared_parameters[position]}){literal}"
        for position, literal in enumerate(literals)
        if position < len(declared_parameters)
    ]
    # A rendering may recover more parameters than the source has; the corpus
    # has no value for those, and passes the zero a caller leaves in a register
    # it never wrote. Fewer is refused earlier as a signature mismatch.
    return converted + [
        f"({declared})0" for declared in declared_parameters[len(literals) :]
    ]


def runner_source(
    function_source: str,
    blobs: list[str],
    name: str,
    spec: FunctionSpec | ScalarSpec,
    cases: list[dict[str, Any]],
    *,
    diagnostic: bool,
    callee_sources: list[str] | None = None,
    declared_parameters: list[str] | None = None,
) -> str:
    arrays = []
    arms = []
    for index, case in enumerate(cases):
        if isinstance(spec, ScalarSpec):
            args = scalar_case_arguments(
                case,
                diagnostic=diagnostic,
                declared_parameters=declared_parameters,
            )
            callee = f"dec_{name}"
            call = f"{callee}({', '.join(args)})"
            arms.append(
                f"case {index}u: printf(\"%0{spec.printf_width}\" PRIx{spec.result_bits} \"\\n\", "
                f"({spec.c_result_type})({call})); return 0;"
            )
            continue
        data = bytes.fromhex(case["bytes"])
        initializer = ",".join(str(byte) for byte in data) if data else "0"
        arrays.append(f"static unsigned char case_{index}[] = {{{initializer}}};")
        args = [f"case_{index}", f"{case['length']}u"]
        if spec.arity == 3:
            args.append(f"UINT32_C({case['seed']})")
        if diagnostic:
            # The diagnostic path widens on purpose, but a parameter the
            # rendering declared a pointer stays one -- the signature keeps it,
            # so the call has to pass one. Only the integers become `long`.
            def diagnostic_argument(index: int, argument: str) -> str:
                declared = (
                    declared_parameters[index]
                    if declared_parameters is not None
                    and index < len(declared_parameters)
                    else ""
                )
                if "*" in declared:
                    return f"({declared})(uintptr_t){argument}"
                if index == 0:
                    return f"(long)(uintptr_t){argument}"
                return f"(long){argument}"

            args = [
                diagnostic_argument(index, argument)
                for index, argument in enumerate(args)
            ]
        elif declared_parameters is not None and len(declared_parameters) >= len(args):
            # Call through the signature the rendering declares. The pointer is
            # converted the same way the machine passes it, as an integer of the
            # declared width.
            #
            # A rendering may declare more parameters than the source has. The
            # decompiler recovers the machine's own interface, and radare2's
            # argument detection counts a register the function writes without
            # reading -- `xor edx, edx` at -O2 makes `edx` look like an argument.
            # Slots the corpus has no value for are passed zero, which is what
            # the caller leaves in a register it never set, and the difference
            # is reported by the typed-recovery score rather than blocking the
            # run.
            positional = [f"({declared_parameters[0]})(uintptr_t){args[0]}"] + [
                f"({declared_parameters[position]}){arg}"
                for position, arg in enumerate(args[1:], start=1)
            ]
            args = positional + [
                f"({declared})0" for declared in declared_parameters[len(args) :]
            ]
        callee = f"dec_{name}"
        call = f"{callee}({', '.join(args)})"
        arms.append(
            f"case {index}u: printf(\"%0{spec.printf_width}\" PRIx{spec.result_bits} \"\\n\", "
            f"({spec.c_result_type})({call})); return 0;"
        )
    # The raw score proves the emitted C compiles strictly and runs. Whether its
    # declared signature equals the source's own types is a separate question,
    # reported as the typed-recovery score, because the decompiler documents
    # that it never claims pointer-ness or signedness.
    type_check: list[str] = []
    return "\n".join(
        [
            "#include <inttypes.h>",
            "#include <stddef.h>",
            "#include <stdint.h>",
            "#include <stdio.h>",
            "#include <stdlib.h>",
            BITVECTOR_PRELUDE,
            *blobs,
            *arrays,
            *(callee_sources or []),
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
    oracle: Path, name: str, spec: FunctionSpec | ScalarSpec, case: dict[str, Any]
) -> dict[str, Any]:
    if isinstance(spec, ScalarSpec):
        command = [str(oracle), name, *(f"0x{value:x}" for value in case["arguments"])]
        result = run_command(command, timeout=3)
        if result["status"] == "pass":
            result["value"] = result["stdout"].strip().lower()
        return result
    payload = case["bytes"] or "-"
    command = [str(oracle), name, payload]
    if spec.arity == 3:
        command.append(str(case["seed"]))
    result = run_command(command, timeout=3)
    if result["status"] == "pass":
        result["value"] = result["stdout"].strip().lower()
    return result


def load_baseline(path: Path, specs: dict[str, Any] | None = None) -> dict[str, str]:
    specs = SPECS if specs is None else specs
    if not path.exists():
        return {}
    data = json.loads(path.read_text())
    if data.get("schema_version") != 1 or not isinstance(data.get("raw_sha256"), dict):
        raise ValueError(f"unsupported baseline manifest: {path}")
    baseline = {str(key): str(value) for key, value in data["raw_sha256"].items()}
    expected = {
        f"{config}/{function}" for config in CONFIGS for function in specs
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
    corpus_prefix = "" if args.corpus == "hashes" else f"{args.corpus}_"
    raw_dir = artifact_root / "raw"
    compile_dir = artifact_root / "compile" / f"{corpus_prefix}{args.config}"
    raw_dir.mkdir(parents=True, exist_ok=True)
    compile_dir.mkdir(parents=True, exist_ok=True)
    specs = CORPUS_SPECS[args.corpus]
    baseline = load_baseline(args.baseline, specs)
    entries: list[dict[str, Any]] = []

    for name, spec in specs.items():
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
            "effect_obligations": {"status": "missing", "marker_count": 0},
            "placement_audit": {"status": "missing", "marker_count": 0},
            "render_refusal": {"status": "missing", "marker_count": 0},
            "machine_noise": {"status": "missing"},
        }
        found = sections.get(name, [])
        entry["generation"]["section_count"] = len(found)
        if len(found) != 1:
            entry["generation"]["status"] = "missing" if not found else "duplicate"
            entries.append(entry)
            continue
        (
            exact_section,
            entry["binding_audit"],
            entry["effect_obligations"],
            entry["placement_audit"],
            entry["render_refusal"],
        ) = parse_render_audits(found[0])
        section_dir = artifact_root / "raw-sections"
        section_dir.mkdir(parents=True, exist_ok=True)
        section_path = section_dir / f"{corpus_prefix}{args.config}_{name}.txt"
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
                {
                    "status": terminal_status,
                    "error": terminal_error,
                    "fallback_reason": fallback_reason(exact_section),
                }
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

        entry["machine_noise"] = _score_machine_noise(raw_source, args.config)

        raw_path = raw_dir / f"{corpus_prefix}{args.config}_{name}.c"
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

        # Fewer parameters than the corpus must pass is a real mismatch: there is
        # no way to hand the function its inputs. More is recovery imprecision,
        # measured by the typed-recovery score and called through below.
        if arity is None or arity < spec.arity or linkage_rewrite["count"] != 1:
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

        declared_parameters = rendered_parameter_types(normalized)
        declared_return = rendered_return_type(normalized, name)
        if isinstance(spec, ScalarSpec):
            expected_parameters = ["uint64_t"] * spec.arity
        else:
            expected_parameters = ["const uint8_t *", "size_t"]
            if spec.arity == 3:
                expected_parameters.append("uint32_t")
        # Reported, never gating: whether the rendering's own signature equals
        # the source's types is the typed-recovery question, and the decompiler
        # documents that it does not claim them.
        entry["typed_recovery"] = {
            "declared_parameters": declared_parameters,
            "declared_return": declared_return,
            "expected_parameters": expected_parameters,
            "expected_return": spec.c_result_type,
            "parameters_match": declared_parameters == expected_parameters,
            "return_matches": declared_return == spec.c_result_type,
        }
        callee_sources, callee_notes = callee_definitions(
            sections, raw_mapped, root=name
        )
        if callee_notes:
            entry["callees"] = callee_notes
        raw_program = runner_source(
            raw_mapped,
            raw_blobs,
            name,
            spec,
            cases,
            diagnostic=False,
            callee_sources=callee_sources,
            declared_parameters=declared_parameters,
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
                callee_sources=callee_definitions(
                    sections, diagnostic_mapped, root=name
                )[0],
                declared_parameters=declared_parameters,
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

        # One case decides whether the diagnostic path even produces the right
        # answer, reported separately from the differential's full sweep. The
        # buffer corpus uses its historical message; a scalar corpus has no
        # such case and uses its first argument vector.
        legacy_index = (
            0
            if isinstance(spec, ScalarSpec)
            else next(
                index
                for index, case in enumerate(cases)
                if case["length"] == len(LEGACY_MESSAGE)
                and case["seed"] == spec.default_seed
            )
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
                    # A case that never produced an answer and a case that
                    # produced the wrong one are different findings. Both fail
                    # the gate, and only one of them says the decompiler is
                    # wrong: a timeout under machine load reported as `failed`
                    # teaches a reader to disbelieve the column.
                    differential_status = (
                        "timeout"
                        if case_status == "timeout" and differential_status != "failed"
                        else "failed"
                    )
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
        "corpus": args.corpus,
        "expected_entries": len(specs),
        "input": str(args.input),
        "binary": str(args.binary),
        "oracle": str(args.oracle),
        "strict_c_flags": list(STRICT_C_FLAGS),
        "entries": entries,
    }


def print_summary(report: dict[str, Any]) -> None:
    print(
        f"== {report.get('corpus', 'hashes')}/{report['config']} "
        f"({len(report['entries'])}/{report['expected_entries']} cells)"
    )
    for entry in report["entries"]:
        print(
            f"  {entry['function']:<15}"
            f"gen={entry['generation']['status']:<10} "
            f"raw={entry['raw']['status']:<18} "
            f"diag={entry['diagnostic']['status']:<18} "
            f"diff={entry['differential']['status']:<16} "
            f"basis={str(entry['differential'].get('basis')):<10} "
            f"snapshot={entry['snapshot']['status']:<10} "
            f"binding_audit={entry['binding_audit']['status']:<12} "
            f"effect_obligations={entry['effect_obligations']['status']:<12} "
            f"placement_audit={entry['placement_audit']['status']:<12} "
            f"render_refusal={entry['render_refusal']['status']:<12} "
            f"machine_noise={entry['machine_noise']['status']}"
        )
        noise = entry["machine_noise"]
        if noise.get("failing"):
            detail = " ".join(
                f"{name}={noise['counts'][name]}" for name in noise["failing"]
            )
            print(f"    machine_noise: {detail}")
        if entry["raw"].get("status") == "failed":
            print(f"    raw: {first_error(entry['raw'])}")
        if entry["diagnostic"].get("status") in {"failed", "wrong"}:
            print(f"    diagnostic: {first_error(entry['diagnostic'])}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("config", choices=tuple(CONFIGS))
    parser.add_argument(
        "--corpus",
        choices=tuple(CORPUS_SPECS),
        default="hashes",
        help="which corpus source's functions to score",
    )
    parser.add_argument("--input", type=Path)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--oracle", type=Path)
    parser.add_argument("--artifact-root", type=Path, default=ROOT / "artifacts")
    parser.add_argument("--baseline", type=Path)
    args = parser.parse_args()
    # The hash corpus keeps its historical file names so nothing that reads its
    # artifacts has to learn a new layout; every other corpus is named.
    prefix = "" if args.corpus == "hashes" else f"{args.corpus}_"
    binary_stem = CONFIGS[args.config] if args.corpus == "hashes" else (
        f"{args.corpus}_{args.config}"
    )
    if args.baseline is None:
        args.baseline = ROOT / (
            "raw-baseline-sha256.json"
            if args.corpus == "hashes"
            else f"raw-baseline-{args.corpus}-sha256.json"
        )
    args.input = args.input or (
        args.artifact_root / "dumps" / f"{prefix}out_{args.config}.txt"
    )
    args.binary = args.binary or args.artifact_root / "bin" / binary_stem
    args.oracle = args.oracle or (
        args.artifact_root / "bin" / f"{prefix}oracle_{args.config}"
    )
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
    prefix = "" if args.corpus == "hashes" else f"{args.corpus}_"
    result_path = result_dir / f"{prefix}{args.config}.json"
    result_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print_summary(report)
    print(f"  report={result_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
