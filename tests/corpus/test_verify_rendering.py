#!/usr/bin/env python3
"""Unit tests for the corpus verifier's deterministic, tool-free contracts."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_binding_audit_schema as schema_checker  # noqa: E402
import verify_rendering as verifier  # noqa: E402


class MarkedSectionTests(unittest.TestCase):
    def test_discovers_every_section_and_preserves_duplicates(self) -> None:
        dump = """ignored prelude
R2SLEIGH_CORPUS_BEGIN__fnv1a32
first fnv rendering
R2SLEIGH_CORPUS_END__fnv1a32
R2SLEIGH_CORPUS_BEGIN__djb2
djb rendering
R2SLEIGH_CORPUS_END__djb2
R2SLEIGH_CORPUS_BEGIN__fnv1a32
second fnv rendering
R2SLEIGH_CORPUS_END__fnv1a32
ignored epilogue
"""

        self.assertEqual(
            verifier.marked_sections(dump),
            {
                "fnv1a32": [
                    "first fnv rendering\n",
                    "second fnv rendering\n",
                ],
                "djb2": ["djb rendering\n"],
            },
        )

    def test_section_hash_preserves_leading_blank_line_count(self) -> None:
        one_leading_newline = """R2SLEIGH_CORPUS_BEGIN__fnv1a32
body
R2SLEIGH_CORPUS_END__fnv1a32
"""
        two_leading_newlines = """R2SLEIGH_CORPUS_BEGIN__fnv1a32

body
R2SLEIGH_CORPUS_END__fnv1a32
"""

        first = verifier.marked_sections(one_leading_newline)["fnv1a32"][0]
        second = verifier.marked_sections(two_leading_newlines)["fnv1a32"][0]

        self.assertEqual(first, "body\n")
        self.assertEqual(second, "\nbody\n")
        self.assertNotEqual(verifier.sha256_text(first), verifier.sha256_text(second))

    def test_exact_text_io_preserves_crlf_for_hashing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "dump.txt"
            path.write_bytes(b"line one\r\nline two\r\n")

            crlf = verifier.read_exact_text(path)
            lf = crlf.replace("\r\n", "\n")

            self.assertEqual(crlf, "line one\r\nline two\r\n")
            self.assertNotEqual(verifier.sha256_text(crlf), verifier.sha256_text(lf))


class BindingAuditTests(unittest.TestCase):
    def test_typed_cause_oracle_requires_exact_unique_schema_coverage(self) -> None:
        schema = {
            "no_fields": frozenset(),
            "one_field": frozenset({"value_id"}),
        }
        with mock.patch.object(
            verifier, "BINDING_AUDIT_JOURNAL_CAUSE_FIELDS", schema
        ):
            self.assertEqual(
                schema_checker.validate_oracle(
                    [
                        {"kind": "no_fields"},
                        {"kind": "one_field", "value_id": 7},
                    ]
                ),
                2,
            )
            malformed = [
                [{"kind": "no_fields"}],
                [{"kind": "no_fields"}, {"kind": "no_fields"}],
                [
                    {"kind": "no_fields"},
                    {"kind": "one_field", "value_id": 7, "legacy": 1},
                ],
            ]
            for candidate in malformed:
                with self.subTest(candidate=candidate):
                    with self.assertRaises(verifier.BindingAuditFormatError):
                        schema_checker.validate_oracle(candidate)

    def test_placement_cause_oracle_requires_exact_unique_schema_coverage(self) -> None:
        schema = {
            "no_fields": frozenset(),
            "one_field": frozenset({"binding_index"}),
        }
        with mock.patch.object(verifier, "PLACEMENT_AUDIT_CAUSE_FIELDS", schema):
            self.assertEqual(
                schema_checker.validate_placement_oracle(
                    [
                        {"kind": "no_fields"},
                        {"kind": "one_field", "binding_index": 7},
                    ]
                ),
                2,
            )
            for candidate in (
                [{"kind": "no_fields"}],
                [{"kind": "no_fields"}, {"kind": "no_fields"}],
                [
                    {"kind": "no_fields"},
                    {"kind": "one_field", "binding_index": 7, "legacy": 1},
                ],
            ):
                with self.subTest(candidate=candidate):
                    with self.assertRaises(verifier.BindingAuditFormatError):
                        schema_checker.validate_placement_oracle(candidate)

    @staticmethod
    def admitted_effect_record() -> dict[str, object]:
        return {
            "schema_version": 1,
            "status": "admitted",
            "total": 3,
            "rendered": 2,
            "justified_elision": 1,
            "refused": 0,
            "unaccounted": 0,
            "conflicts": 0,
        }

    @staticmethod
    def applied_placement_record() -> dict[str, object]:
        return {"schema_version": 1, "status": "applied"}

    @staticmethod
    def no_render_refusal_record() -> dict[str, object]:
        return {"schema_version": 1, "status": "none"}

    @staticmethod
    def complete_record() -> dict[str, object]:
        observations = {
            domain: {
                "total": 3,
                "rendered": 2,
                "justified_elision": 1,
                "refused": 0,
                "unaccounted": 0,
            }
            for domain in verifier.BINDING_AUDIT_DOMAINS
        }
        shadow = {
            domain: {
                "total": 3,
                "observed": 3,
                "agree_correct": 2,
                "old_wrong": 1,
                "shadow_wrong": 0,
                "both_wrong_equal": 0,
                "both_wrong_different": 0,
                "unclassified": 0,
                "refused": 0,
            }
            for domain in verifier.BINDING_AUDIT_DOMAINS
        }
        return {
            "schema_version": 5,
            "request_status": "completed",
            "audit": {
                "schema_version": 2,
                "status": "complete",
                "observations": observations,
                "shadow": shadow,
            },
            "effect_obligations": BindingAuditTests.admitted_effect_record(),
            "placement_audit": BindingAuditTests.applied_placement_record(),
            "render_refusal": BindingAuditTests.no_render_refusal_record(),
        }

    @classmethod
    def marker(cls, record: dict[str, object] | None = None) -> str:
        payload = record if record is not None else cls.complete_record()
        return verifier.BINDING_AUDIT_PREFIX + json.dumps(
            payload, separators=(",", ":")
        )

    def test_exact_marker_is_removed_and_all_ledgers_are_recomputed(self) -> None:
        section = f"rendered C\n{self.marker()}\ndiagnostic tail\n"

        cleaned, score, effect_score, placement_score, render_score = (
            verifier.parse_render_audits(section)
        )

        self.assertEqual(cleaned, "rendered C\ndiagnostic tail\n")
        self.assertEqual(score["status"], "pass")
        self.assertEqual(score["marker_count"], 1)
        self.assertTrue(all(score["equations"]["observations"].values()))
        self.assertTrue(all(score["equations"]["shadow"].values()))
        self.assertTrue(all(score["equations"]["totals_match"].values()))
        self.assertTrue(all(score["quality"]["observations"].values()))
        self.assertTrue(all(score["quality"]["shadow"].values()))
        self.assertEqual(effect_score["status"], "pass")
        self.assertTrue(effect_score["equation_balanced"])
        self.assertTrue(all(effect_score["quality"].values()))
        self.assertEqual(placement_score["status"], "pass")
        self.assertEqual(render_score["status"], "pass")

    def test_render_refusal_is_typed_and_never_scores_as_a_pass(self) -> None:
        record = self.complete_record()
        record["request_status"] = "refused"
        record["render_refusal"] = {
            "schema_version": 1,
            "status": "refused",
            "kind": "missing_program_variable_authorization",
        }

        _, binding, effect, placement, render = verifier.parse_render_audits(
            self.marker(record) + "\n"
        )

        self.assertEqual(binding["request_status"], "refused")
        self.assertEqual(effect["request_status"], "refused")
        self.assertEqual(placement["request_status"], "refused")
        self.assertEqual(render["status"], "refused")
        self.assertEqual(render["source_status"], "refused")

    def test_admission_refusal_envelopes_preserve_exact_causes_and_counts(self) -> None:
        observation_refusal = self.complete_record()
        observation_refusal["request_status"] = "refused"
        observations = observation_refusal["audit"]["observations"]
        observations["values"].update(
            {"rendered": 1, "justified_elision": 1, "refused": 1}
        )
        observation_refusal["audit"] = {
            "schema_version": 2,
            "status": "non_quality_observations",
            "observations": observations,
        }
        observation_refusal["render_refusal"] = {
            "schema_version": 1,
            "status": "refused",
            "kind": "refused_binding_disposition",
            "observations": observations,
        }

        _, binding, _, _, render = verifier.parse_render_audits(
            self.marker(observation_refusal) + "\n"
        )

        self.assertEqual(binding["status"], "non_quality")
        self.assertEqual(binding["source_status"], "non_quality_observations")
        self.assertEqual(
            binding["record"]["audit"]["observations"]["values"]["refused"],
            1,
        )
        self.assertFalse(binding["quality"]["observations"]["values"])
        self.assertEqual(render["status"], "refused")
        self.assertEqual(
            render["record"]["render_refusal"]["observations"]["values"][
                "refused"
            ],
            1,
        )

        placement_refusal = self.complete_record()
        placement_refusal["request_status"] = "refused"
        cause = {
            "kind": "read_before_assignment",
            "binding_index": 7,
            "instruction_id": 11,
            "input_index": 13,
        }
        placement_refusal["audit"] = {
            "schema_version": 2,
            "status": "failed",
            "reason": "placement_refusal",
            "cause": cause,
        }
        placement_refusal["placement_audit"] = {
            "schema_version": 1,
            "status": "refused",
            "cause": cause,
        }
        placement_refusal["render_refusal"] = {
            "schema_version": 1,
            "status": "refused",
            "kind": "read_before_assignment",
            "cause": cause,
        }

        _, binding, _, placement, render = verifier.parse_render_audits(
            self.marker(placement_refusal) + "\n"
        )

        self.assertEqual(binding["status"], "failed")
        self.assertEqual(binding["record"]["audit"]["cause"], cause)
        self.assertEqual(placement["status"], "refused")
        self.assertEqual(render["status"], "refused")
        self.assertEqual(render["record"]["render_refusal"]["cause"], cause)

    def test_admission_refusal_envelopes_reject_parallel_or_mismatched_fields(self) -> None:
        observation_refusal = self.complete_record()
        observations = observation_refusal["audit"]["observations"]
        observation_refusal["audit"] = {
            "schema_version": 2,
            "status": "non_quality_observations",
            "observations": observations,
            "shadow": observation_refusal["audit"]["shadow"],
        }
        _, binding = verifier.parse_binding_audit(
            self.marker(observation_refusal) + "\n"
        )
        self.assertEqual(binding["status"], "malformed")

        placement_refusal = self.complete_record()
        placement_refusal["request_status"] = "refused"
        placement_refusal["audit"] = {
            "schema_version": 2,
            "status": "failed",
            "reason": "placement_refusal",
            "cause": {"kind": "missing_definition", "binding_index": 17},
        }
        placement_refusal["render_refusal"] = {
            "schema_version": 1,
            "status": "refused",
            "kind": "missing_definition",
            "cause": {"kind": "missing_definition", "binding_index": 17},
            "legacy": True,
        }
        _, binding, _, _, render = verifier.parse_render_audits(
            self.marker(placement_refusal) + "\n"
        )
        self.assertEqual(binding["status"], "failed")
        self.assertEqual(render["status"], "malformed")

        mismatch = json.loads(json.dumps(placement_refusal))
        del mismatch["render_refusal"]["legacy"]
        mismatch["render_refusal"]["kind"] = "read_before_assignment"
        _, _, _, _, render = verifier.parse_render_audits(self.marker(mismatch) + "\n")
        self.assertEqual(render["status"], "malformed")

    def test_refused_request_without_render_reason_is_not_a_render_pass(self) -> None:
        record = self.complete_record()
        record["request_status"] = "refused"

        _, _, _, _, render = verifier.parse_render_audits(self.marker(record) + "\n")

        self.assertEqual(render["status"], "non_quality")
        self.assertEqual(render["source_status"], "none")
        self.assertEqual(render["request_status"], "refused")

    def test_effect_schema_checker_requires_exact_typed_counts(self) -> None:
        effect = self.admitted_effect_record()
        self.assertEqual(schema_checker.validate_effect_obligations(effect), effect)
        self.assertEqual(schema_checker.validate_schema(effect), 1)

        malformed = []
        missing = dict(effect)
        del missing["conflicts"]
        malformed.append(missing)
        extra = dict(effect)
        extra["accounted"] = 3
        malformed.append(extra)
        wrong_version = dict(effect)
        wrong_version["schema_version"] = 2
        malformed.append(wrong_version)
        boolean_count = dict(effect)
        boolean_count["total"] = True
        malformed.append(boolean_count)
        unknown_status = dict(effect)
        unknown_status["status"] = "complete"
        malformed.append(unknown_status)

        for candidate in malformed:
            with self.subTest(candidate=candidate):
                with self.assertRaises(verifier.BindingAuditFormatError):
                    schema_checker.validate_effect_obligations(candidate)

    def test_placement_audit_scores_all_states_and_requires_exact_typed_causes(self) -> None:
        cases = (
            ({"schema_version": 1, "status": "applied"}, "pass"),
            ({"schema_version": 1, "status": "not_run"}, "not_run"),
            (
                {
                    "schema_version": 1,
                    "status": "refused",
                    "cause": {
                        "kind": "read_before_assignment",
                        "binding_index": 2,
                        "instruction_id": 7,
                        "input_index": 1,
                    },
                },
                "refused",
            ),
        )
        for placement, expected in cases:
            with self.subTest(status=expected):
                record = self.complete_record()
                record["placement_audit"] = placement
                _, binding, effect, scored, _ = verifier.parse_render_audits(
                    self.marker(record) + "\n"
                )
                self.assertEqual(binding["status"], "pass")
                self.assertEqual(effect["status"], "pass")
                self.assertEqual(scored["status"], expected)

        for cause in (
            {"kind": "read_before_assignment", "binding_index": 2},
            {
                "kind": "read_before_assignment",
                "binding_index": 2,
                "instruction_id": 7,
                "input_index": 1,
                "debug": "private error text",
            },
            {"kind": "unknown"},
        ):
            with self.subTest(cause=cause):
                record = self.complete_record()
                record["placement_audit"] = {
                    "schema_version": 1,
                    "status": "refused",
                    "cause": cause,
                }
                _, binding, effect, placement, _ = verifier.parse_render_audits(
                    self.marker(record) + "\n"
                )
                self.assertEqual(binding["status"], "pass")
                self.assertEqual(effect["status"], "pass")
                self.assertEqual(placement["status"], "malformed")

    def test_sidecar_requires_v4_and_all_independent_audits(self) -> None:
        missing_effect = self.complete_record()
        del missing_effect["effect_obligations"]
        missing_placement = self.complete_record()
        del missing_placement["placement_audit"]
        old_version = self.complete_record()
        old_version["schema_version"] = 3
        extra = self.complete_record()
        extra["legacy"] = None

        for candidate in (missing_effect, missing_placement, old_version, extra):
            with self.subTest(candidate=candidate):
                _, binding_score, effect_score, placement_score, _ = verifier.parse_render_audits(
                    self.marker(candidate) + "\n"
                )
                self.assertEqual(binding_score["status"], "malformed")
                self.assertEqual(effect_score["status"], "malformed")
                self.assertEqual(placement_score["status"], "malformed")

    def test_effect_gate_requires_admission_balance_and_zero_defects(self) -> None:
        mutations = {
            "unbalanced": lambda effect: effect.update({"total": 4}),
            "refused_count": lambda effect: effect.update(
                {"justified_elision": 0, "refused": 1}
            ),
            "unaccounted": lambda effect: effect.update(
                {"justified_elision": 0, "unaccounted": 1}
            ),
            "conflict": lambda effect: effect.update({"conflicts": 1}),
            "refused_status": lambda effect: effect.update({"status": "refused"}),
            "not_run": lambda effect: effect.update(
                {
                    "status": "not_run",
                    "total": 0,
                    "rendered": 0,
                    "justified_elision": 0,
                }
            ),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                record = self.complete_record()
                mutate(record["effect_obligations"])
                _, binding_score, effect_score, placement_score, _ = verifier.parse_render_audits(
                    self.marker(record) + "\n"
                )
                self.assertEqual(binding_score["status"], "pass")
                self.assertEqual(placement_score["status"], "pass")
                expected_status = {
                    "refused_status": "refused",
                    "not_run": "not_run",
                }.get(label, "non_quality")
                self.assertEqual(effect_score["status"], expected_status)

    def test_binding_and_effect_payload_failures_are_scored_independently(self) -> None:
        malformed_binding = self.complete_record()
        malformed_binding["audit"]["legacy"] = True
        _, binding_score, effect_score, placement_score, _ = verifier.parse_render_audits(
            self.marker(malformed_binding) + "\n"
        )
        self.assertEqual(binding_score["status"], "malformed")
        self.assertEqual(effect_score["status"], "pass")
        self.assertEqual(placement_score["status"], "pass")

        malformed_effect = self.complete_record()
        malformed_effect["effect_obligations"]["legacy"] = True
        _, binding_score, effect_score, placement_score, _ = verifier.parse_render_audits(
            self.marker(malformed_effect) + "\n"
        )
        self.assertEqual(binding_score["status"], "pass")
        self.assertEqual(effect_score["status"], "malformed")
        self.assertEqual(placement_score["status"], "pass")

    def test_zero_effects_can_be_admitted_when_the_ledger_is_closed(self) -> None:
        record = self.complete_record()
        record["effect_obligations"].update(
            {
                "total": 0,
                "rendered": 0,
                "justified_elision": 0,
            }
        )

        _, _, effect_score, _, _ = verifier.parse_render_audits(
            self.marker(record) + "\n"
        )

        self.assertEqual(effect_score["status"], "pass")
        self.assertTrue(effect_score["equation_balanced"])

    def test_missing_duplicate_and_malformed_markers_are_distinct(self) -> None:
        marker = self.marker()
        cases = {
            "missing": ("rendered C\n", "rendered C\n", 0),
            "duplicate": (
                f"rendered C\n{marker}\n{marker}\n",
                "rendered C\n",
                2,
            ),
            "malformed": (
                f"rendered C\n{verifier.BINDING_AUDIT_PREFIX}{{bad json}}\n",
                "rendered C\n",
                1,
            ),
        }
        for expected_status, (section, expected_cleaned, count) in cases.items():
            with self.subTest(status=expected_status):
                cleaned, score, effect_score, placement_score, _ = verifier.parse_render_audits(section)
                self.assertEqual(cleaned, expected_cleaned)
                self.assertEqual(score["status"], expected_status)
                self.assertEqual(score["marker_count"], count)
                self.assertEqual(effect_score["status"], expected_status)
                self.assertEqual(effect_score["marker_count"], count)
                self.assertEqual(placement_score["status"], expected_status)
                self.assertEqual(placement_score["marker_count"], count)

    def test_balanced_unaccounted_refusal_or_shadow_defect_cannot_pass(self) -> None:
        mutations = {
            "unaccounted": lambda record: record["audit"]["observations"][
                "values"
            ].update(
                {"justified_elision": 0, "unaccounted": 1}
            ),
            "observation_refusal": lambda record: record["audit"]["observations"][
                "uses"
            ].update(
                {"justified_elision": 0, "refused": 1}
            ),
            "shadow_wrong": lambda record: record["audit"]["shadow"]["writes"].update(
                {"agree_correct": 1, "shadow_wrong": 1}
            ),
            "shadow_refusal": lambda record: record["audit"]["shadow"]["values"].update(
                {"refused": 1}
            ),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                record = self.complete_record()
                mutate(record)
                _, score = verifier.parse_binding_audit(self.marker(record) + "\n")
                self.assertEqual(score["status"], "non_quality")

    def test_counted_producer_failure_keeps_counts_but_cannot_pass(self) -> None:
        record = self.complete_record()
        record["audit"]["status"] = "incomplete_observations"
        record["audit"]["observations"]["values"].update(
            {"justified_elision": 0, "unaccounted": 1}
        )

        _, score = verifier.parse_binding_audit(self.marker(record) + "\n")

        self.assertEqual(score["status"], "non_quality")
        self.assertEqual(score["source_status"], "incomplete_observations")
        self.assertEqual(
            score["record"]["audit"]["observations"]["values"]["unaccounted"],
            1,
        )
        self.assertTrue(score["equations"]["observations"]["values"])

    def test_category_equation_or_extra_count_fields_are_not_trusted(self) -> None:
        unbalanced = self.complete_record()
        unbalanced["audit"]["observations"]["values"]["total"] = 4
        _, score = verifier.parse_binding_audit(self.marker(unbalanced) + "\n")
        self.assertEqual(score["status"], "non_quality")
        self.assertFalse(score["equations"]["observations"]["values"])

        extra = self.complete_record()
        extra["audit"]["observations"]["values"]["accounted"] = 3
        _, score = verifier.parse_binding_audit(self.marker(extra) + "\n")
        self.assertEqual(score["status"], "malformed")

    def test_individual_audits_remain_diagnostic_when_request_is_refused(self) -> None:
        record = self.complete_record()
        record["request_status"] = "refused"

        _, score, effect_score, placement_score, _ = verifier.parse_render_audits(
            self.marker(record) + "\n"
        )

        self.assertEqual(score["status"], "pass")
        self.assertEqual(score["request_status"], "refused")
        self.assertTrue(all(score["quality"]["observations"].values()))
        self.assertTrue(all(score["quality"]["shadow"].values()))
        self.assertEqual(effect_score["status"], "pass")
        self.assertEqual(effect_score["request_status"], "refused")
        self.assertEqual(placement_score["status"], "pass")
        self.assertEqual(placement_score["request_status"], "refused")

    def test_failed_journal_audit_requires_an_exact_typed_cause(self) -> None:
        record = {
            "schema_version": 5,
            "request_status": "completed",
            "audit": {
                "schema_version": 2,
                "status": "failed",
                "reason": "journal_seal_failure",
                "cause": {
                    "kind": "observation_out_of_range",
                    "observation_id": 7,
                    "expected_count": 5,
                },
            },
            "effect_obligations": self.admitted_effect_record(),
            "placement_audit": self.applied_placement_record(),
            "render_refusal": self.no_render_refusal_record(),
        }

        _, score = verifier.parse_binding_audit(self.marker(record) + "\n")

        self.assertEqual(score["status"], "failed")
        self.assertEqual(
            score["record"]["audit"]["cause"],
            record["audit"]["cause"],
        )

        construction = json.loads(json.dumps(record))
        construction["audit"]["reason"] = "journal_construction_failure"
        _, construction_score = verifier.parse_binding_audit(
            self.marker(construction) + "\n"
        )
        self.assertEqual(construction_score["status"], "failed")
        self.assertEqual(
            construction_score["record"]["audit"]["cause"],
            record["audit"]["cause"],
        )

        recording = json.loads(json.dumps(record))
        recording["audit"]["reason"] = "journal_recording_failure"
        _, recording_score = verifier.parse_binding_audit(
            self.marker(recording) + "\n"
        )
        self.assertEqual(recording_score["status"], "failed")
        self.assertEqual(
            recording_score["record"]["audit"]["cause"],
            record["audit"]["cause"],
        )

        machine = json.loads(json.dumps(record))
        machine["audit"]["cause"] = {
            "kind": "binding_plan_machine_width_mismatch",
            "instruction_id": 11,
            "expected_bits": 64,
            "actual_bits": 32,
        }
        _, machine_score = verifier.parse_binding_audit(self.marker(machine) + "\n")
        self.assertEqual(machine_score["status"], "failed")
        self.assertEqual(
            machine_score["record"]["audit"]["cause"],
            machine["audit"]["cause"],
        )

        malformed = []
        collapsed = json.loads(json.dumps(record))
        collapsed["audit"]["cause"] = {"kind": "binding_plan"}
        malformed.append(collapsed)
        missing = json.loads(json.dumps(record))
        del missing["audit"]["cause"]
        malformed.append(missing)
        extra = json.loads(json.dumps(record))
        extra["audit"]["cause"]["unexpected"] = 1
        malformed.append(extra)
        wrong_fields = json.loads(json.dumps(record))
        del wrong_fields["audit"]["cause"]["expected_count"]
        malformed.append(wrong_fields)
        unknown = json.loads(json.dumps(record))
        unknown["audit"]["cause"] = {"kind": "unknown"}
        malformed.append(unknown)
        for reason in [
            "journal_failure",
            "binding_plan_failure",
            "legacy_collapsed_failure",
        ]:
            unknown_reason = json.loads(json.dumps(record))
            unknown_reason["audit"]["reason"] = reason
            del unknown_reason["audit"]["cause"]
            malformed.append(unknown_reason)

        for candidate in malformed:
            with self.subTest(candidate=candidate):
                _, rejected = verifier.parse_binding_audit(
                    self.marker(candidate) + "\n"
                )
                self.assertEqual(rejected["status"], "malformed")

    def test_all_zero_complete_audit_cannot_pass(self) -> None:
        record = self.complete_record()
        for domain in verifier.BINDING_AUDIT_DOMAINS:
            record["audit"]["observations"][domain].update(
                {
                    "total": 0,
                    "rendered": 0,
                    "justified_elision": 0,
                    "refused": 0,
                    "unaccounted": 0,
                }
            )
            record["audit"]["shadow"][domain].update(
                {
                    "total": 0,
                    "observed": 0,
                    "agree_correct": 0,
                    "old_wrong": 0,
                }
            )

        _, score = verifier.parse_binding_audit(self.marker(record) + "\n")

        self.assertEqual(score["status"], "non_quality")
        self.assertEqual(score["canonical_total"], 0)
        self.assertFalse(score["quality"]["canonical_nonempty"])


class ExtractionTests(unittest.TestCase):
    def test_extracts_exact_function_with_lexically_ignored_braces(self) -> None:
        expected = """uint32_t sym.fnv1a32(uint8_t *data, uint64_t length)
{
    const char *text = "a } string with an escaped quote: \\\" and {";
    const char closing = '}';
    /* A block comment with } and { must not change nesting. */
    if (length != 0) {
        // A line comment with } must not close the function.
        return data[0];
    }
    return 0;
}
"""
        section = "diagnostic prelude\n" + expected + "diagnostic epilogue\n"

        extracted, error = verifier.extract_function(section, "fnv1a32")

        self.assertIsNone(error)
        self.assertEqual(extracted, expected)


class RewriteTests(unittest.TestCase):
    def test_linkage_normalization_changes_only_the_function_name(self) -> None:
        source = """uint32_t sym.fnv1a32(uint8_t *data, uint64_t length)
{
    uint32_t state = UINT32_C(2166136261);
    state ^= data[0];
    return state + (uint32_t)length;
}
"""
        expected = source.replace("sym.fnv1a32", "dec_fnv1a32", 1)

        normalized, rewrite = verifier.normalize_linkage_name(source, "fnv1a32")

        self.assertEqual(normalized, expected)
        self.assertEqual(
            rewrite,
            {"kind": "linkage_name", "count": 1, "semantic": False},
        )
        self.assertEqual(normalized[normalized.index("{") :], source[source.index("{") :])

    def test_diagnostic_ledger_records_retyping_and_assumed_widths(self) -> None:
        source = """uint32_t sym.fnv1a32(uint8_t *data, uint64_t length)
{
    uint32_t state = 0;
    state += data[0];
    state += *data;
    return state + (uint32_t)length;
}
"""

        repaired, rewrites, assumed_widths = verifier.diagnostic_repair(
            source, "fnv1a32"
        )
        positive = {
            item["kind"]: item
            for item in rewrites
            if item["count"] > 0
        }

        # A recovered pointer parameter keeps its type and its name: retyping
        # it to `long` was the old repair, and component 3 made the emitted
        # declaration good enough that the repair no longer applies to it.
        self.assertIn("long dec_fnv1a32(uint8_t *data, long length)", repaired)
        self.assertIn("long state = 0;", repaired)
        self.assertEqual(assumed_widths, 2)
        for kind in (
            "parameter_retype",
            "return_retype",
            "local_retype",
            "subscript_byte_width",
            "bare_name_deref_byte_width",
        ):
            self.assertIn(kind, positive)
            self.assertIs(positive[kind]["semantic"], True)
        self.assertIs(positive["linkage_name"]["semantic"], False)
        self.assertIn("before_sha256", positive["parameter_retype"])
        self.assertIn("after_sha256", positive["parameter_retype"])


class ImageMappingTests(unittest.TestCase):
    def test_only_evidenced_literal_span_is_rewritten(self) -> None:
        address = 0x100000010
        source = """uint8_t read_table(void)
{
    uint8_t value = *((uint8_t *)0x100000010);
    uintptr_t unrelated_constant = 0x100000010;
    return value + (unrelated_constant != 0);
}
"""
        with mock.patch.object(
            verifier,
            "_json_stdout",
            side_effect=[
                [{"vaddr": 0x100000000, "vsize": 0x100}],
                [],
                [0xAA, 0xBB, 0xCC],
            ],
        ) as json_stdout:
            mapped, blobs, records = verifier.map_image_data(source, Path("unused"))

        self.assertEqual(json_stdout.call_count, 3)
        self.assertIn("*((uint8_t *)((uintptr_t)corpus_blob_0))", mapped)
        self.assertIn("uintptr_t unrelated_constant = 0x100000010;", mapped)
        self.assertEqual(blobs, ["static unsigned char corpus_blob_0[3] = {170,187,204};"])
        self.assertEqual(
            records,
            [
                {
                    "kind": "mapped_image_address",
                    "address": address,
                    "bytes": 3,
                    "count": 1,
                    "semantic": False,
                    "evidence": ["explicit_pointer_cast"],
                }
            ],
        )


class BaselineTests(unittest.TestCase):
    @staticmethod
    def exact_hashes() -> dict[str, str]:
        return {
            f"{config}/{name}": hashlib.sha256(f"{config}/{name}".encode()).hexdigest()
            for config in verifier.CONFIGS
            for name in verifier.SPECS
        }

    def test_exact_baseline_rejects_stale_or_malformed_content(self) -> None:
        exact = self.exact_hashes()
        variants = {
            "stale_key": {**exact, "x64_O0/removed_function": "0" * 64},
            "missing_key": {
                key: value
                for key, value in exact.items()
                if key != "x64_O0/fnv1a32"
            },
            "malformed_key": {
                **{
                    key: value
                    for key, value in exact.items()
                    if key != "x64_O0/fnv1a32"
                },
                "x64_O0:fnv1a32": "0" * 64,
            },
            "malformed_hash": {**exact, "x64_O0/fnv1a32": "not-a-sha256"},
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            valid_path = root / "valid.json"
            valid_path.write_text(
                json.dumps({"schema_version": 1, "raw_sha256": exact})
            )
            self.assertEqual(verifier.load_baseline(valid_path), exact)

            for label, hashes in variants.items():
                with self.subTest(label=label):
                    path = root / f"{label}.json"
                    path.write_text(
                        json.dumps({"schema_version": 1, "raw_sha256": hashes})
                    )
                    with self.assertRaises(ValueError):
                        verifier.load_baseline(path)


class CaseGenerationTests(unittest.TestCase):
    def test_boundary_and_randomized_cases_are_deterministic(self) -> None:
        spec = verifier.SPECS["fnv1a32"]
        random.seed(1)
        first = verifier.cases_for("fnv1a32", spec)
        random.seed(0xDEADBEEF)
        second = verifier.cases_for("fnv1a32", spec)

        self.assertEqual(first, second)
        self.assertEqual(
            [case["length"] for case in first],
            [0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 31, 32, 61, 5, 12, 24, 63, 96],
        )
        self.assertEqual(first[0]["bytes"], "")
        self.assertEqual(first[1]["bytes"], "4c")
        self.assertEqual(first[12]["bytes"], verifier.LEGACY_MESSAGE.hex())
        self.assertEqual(first[13]["bytes"], "480cf2deb6")
        self.assertTrue(all(case["seed"] == spec.default_seed for case in first))

        seeded = verifier.cases_for("murmur3_32", verifier.SPECS["murmur3_32"])
        self.assertEqual(
            [case["seed"] for case in seeded[-5:]],
            [0, 1, 0x9747B28C, 0xFFFFFFFF, 0x13579BDF],
        )
        self.assertEqual(len({case["bytes"] for case in seeded[-5:]}), 1)

    def test_expected_case_ids_and_counts_are_stable(self) -> None:
        common_ids = [
            *(
                f"boundary:{length}"
                for length in (0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 31, 32, 61)
            ),
            *(f"random:{length}" for length in (5, 12, 24, 63, 96)),
        ]
        two_argument = verifier.cases_for("fnv1a32", verifier.SPECS["fnv1a32"])
        murmur = verifier.cases_for("murmur3_32", verifier.SPECS["murmur3_32"])
        xxhash = verifier.cases_for("xxhash32", verifier.SPECS["xxhash32"])

        self.assertEqual(len(two_argument), 18)
        self.assertEqual([case["case_id"] for case in two_argument], common_ids)
        self.assertEqual(len(murmur), 23)
        self.assertEqual(
            [case["case_id"] for case in murmur],
            [
                *common_ids,
                "seed:0",
                "seed:1",
                "seed:2538058380",
                "seed:4294967295",
                "seed:324508639",
            ],
        )
        self.assertEqual(len({case["case_id"] for case in murmur}), len(murmur))
        self.assertEqual(len(xxhash), 22)
        self.assertEqual(
            [case["case_id"] for case in xxhash],
            [
                *common_ids,
                "seed:0",
                "seed:1",
                "seed:4294967295",
                "seed:324508639",
            ],
        )
        self.assertEqual(len({case["case_id"] for case in xxhash}), len(xxhash))


class VerificationTests(unittest.TestCase):
    def test_no_markers_yields_exactly_all_nine_missing_records(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            dump = root / "dump.txt"
            dump.write_text("a dump with no corpus markers\n")
            args = argparse.Namespace(
                config="x64_O0",
                input=dump,
                binary=root / "binary-not-needed",
                oracle=root / "oracle-not-needed",
                artifact_root=root / "artifacts",
                baseline=root / "baseline-not-present.json",
                accept_baseline=False,
            )
            expected_entries = [
                {
                    "config": "x64_O0",
                    "function": name,
                    "generation": {"status": "missing", "section_count": 0},
                    "raw": {"status": "not_run"},
                    "diagnostic": {"status": "not_run"},
                    "differential": {"status": "not_run", "cases": []},
                    "snapshot": {"status": "missing"},
                    "binding_audit": {"status": "missing", "marker_count": 0},
                    "effect_obligations": {
                        "status": "missing",
                        "marker_count": 0,
                    },
                    "placement_audit": {
                        "status": "missing",
                        "marker_count": 0,
                    },
                    "render_refusal": {
                        "status": "missing",
                        "marker_count": 0,
                    },
                    "machine_noise": {"status": "missing"},
                }
                for name in verifier.SPECS
            ]

            with mock.patch.object(
                verifier,
                "run_command",
                side_effect=AssertionError("missing records must not invoke tools"),
            ):
                report = verifier.verify(args)

        self.assertEqual(report["expected_entries"], 9)
        self.assertEqual(len(report["entries"]), 9)
        self.assertEqual(report["entries"], expected_entries)

    def test_renderer_error_section_is_hashed_and_blocks_downstream(self) -> None:
        renderer_error = (
            "ERROR: Cannot snapshot function 'sym._murmur3_32': "
            "the block successors are not coherent\n"
        )
        dump_text = (
            "R2SLEIGH_CORPUS_BEGIN__murmur3_32\n"
            + renderer_error
            + BindingAuditTests.marker()
            + "\n"
            + "R2SLEIGH_CORPUS_END__murmur3_32\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            dump = root / "dump.txt"
            dump.write_text(dump_text)
            args = argparse.Namespace(
                config="x64_O2",
                input=dump,
                binary=root / "binary-not-needed",
                oracle=root / "oracle-not-needed",
                artifact_root=root / "artifacts",
                baseline=root / "baseline-not-present.json",
                accept_baseline=False,
            )

            with mock.patch.object(
                verifier,
                "run_command",
                side_effect=AssertionError("renderer errors must not invoke tools"),
            ):
                report = verifier.verify(args)

            entry = next(
                item for item in report["entries"] if item["function"] == "murmur3_32"
            )
            section_path = Path(entry["generation"]["section_path"])
            self.assertEqual(section_path.read_text(), renderer_error)

        self.assertEqual(len(report["entries"]), 9)
        self.assertEqual(entry["generation"]["status"], "renderer_error")
        self.assertEqual(entry["generation"]["section_count"], 1)
        self.assertEqual(
            entry["generation"]["section_sha256"],
            verifier.sha256_text(renderer_error),
        )
        self.assertEqual(entry["binding_audit"]["status"], "pass")
        self.assertEqual(entry["effect_obligations"]["status"], "pass")
        self.assertEqual(entry["placement_audit"]["status"], "pass")
        for stage in ("raw", "diagnostic", "differential"):
            self.assertEqual(entry[stage]["status"], "blocked_generation")




class MachineNoiseTests(unittest.TestCase):
    """One rendering that spells the machine, one that spells the program.

    Every predicate is exact, so each gets a case that must be counted and a
    case that must not.  The negative cases are deliberately the shapes a
    correct rendering does produce -- a real cast, a real assignment, a real
    call with two arguments -- because a predicate that fires on those would
    make the gate unlandable rather than strict.
    """

    def score(self, source: str, config: str = "x64_O0") -> dict:
        return verifier._score_machine_noise(source, config)

    def test_flag_carrier_is_counted_and_a_named_local_is_not(self) -> None:
        self.assertEqual(
            self.score("uint8_t ZF_21 = (uint8_t)(a == b);")["counts"]["flag_carriers"],
            1,
        )
        self.assertEqual(
            self.score("uint8_t TMPZR_2 = x; uint8_t ZR_2 = TMPZR_2;")["counts"][
                "flag_carriers"
            ],
            2,
        )
        self.assertEqual(
            self.score("uint64_t total_3 = a + b;")["counts"]["flag_carriers"], 0
        )

    def test_self_assignment_through_casts_is_counted(self) -> None:
        self.assertEqual(
            self.score("    X0_7 = (uint64_t)X0_7;")["counts"]["self_assignments"], 1
        )
        self.assertEqual(
            self.score("    RDI_0 = (uint64_t)RDI_0 + (uint64_t)EDX_1;")["counts"][
                "self_assignments"
            ],
            0,
        )

    def test_literal_only_declaration_is_counted(self) -> None:
        self.assertEqual(
            self.score("    uint32_t tmp_6a200_2 = (uint32_t)5;")["counts"][
                "literal_only_declarations"
            ],
            1,
        )
        self.assertEqual(
            self.score("    uint32_t tmp_1 = (uint32_t)(x + 5);")["counts"][
                "literal_only_declarations"
            ],
            0,
        )
        # A program-derived local initialised to a literal is ordinary C; only
        # a carrier this renderer minted for a machine value is machine detail.
        self.assertEqual(
            self.score("    uint64_t total = 0;")["counts"][
                "literal_only_declarations"
            ],
            0,
        )
        self.assertEqual(
            self.score("    uint64_t stack_m40 = 0;")["counts"][
                "literal_only_declarations"
            ],
            0,
        )
        self.assertEqual(
            self.score("    uint64_t RAX_15 = (uint64_t)0x1505;")["counts"][
                "literal_only_declarations"
            ],
            1,
        )

    def test_same_type_cast_is_counted_and_a_widening_pair_is_not(self) -> None:
        self.assertEqual(
            self.score("y = (uint64_t)(uint64_t)x;")["counts"]["same_type_casts"], 1
        )
        # A pointer narrowed to a smaller integer needs the pointer's own width
        # first, so two casts of different types are legitimate.
        self.assertEqual(
            self.score("y = (uint32_t)(uint64_t)p;")["counts"]["same_type_casts"], 0
        )

    def test_cast_chain_of_three_is_counted_and_two_is_not(self) -> None:
        self.assertEqual(
            self.score("y = (uint64_t)(uint32_t)(uint8_t)x;")["counts"]["cast_chains"],
            1,
        )
        self.assertEqual(
            self.score("y = (uint32_t)(uint64_t)p;")["counts"]["cast_chains"], 0
        )

    def test_three_is_allowed_only_as_the_pointer_carrying_shape(self) -> None:
        # Narrow the value, carry it at the address width, make it a pointer.
        # Every step does something C cannot skip.
        self.assertEqual(
            self.score("p = (uint8_t *)(uint64_t)(uint8_t)e;")["counts"][
                "cast_chains"
            ],
            0,
        )
        # The same three widths with the pointer innermost is not that shape:
        # converting a pointer to the type it already has is redundant however
        # long the run around it.
        self.assertEqual(
            self.score("y = (uint32_t)(uint64_t)(uint8_t *)p;")["counts"][
                "cast_chains"
            ],
            1,
        )
        # Four is never the shape.
        self.assertEqual(
            self.score("p = (uint8_t *)(uint64_t)(uint32_t)(uint8_t)e;")["counts"][
                "cast_chains"
            ],
            1,
        )

    def test_comma_condition_is_counted_and_a_two_argument_call_is_not(self) -> None:
        self.assertEqual(
            self.score("while (t = stack_m40, RAX_2 = t, !CF_2) { }")["counts"][
                "comma_conditions"
            ],
            1,
        )
        self.assertEqual(
            self.score("if (memcmp(a, b) == 0) { }")["counts"]["comma_conditions"], 0
        )

    def test_goto_is_gated_only_where_structure_is_claimed(self) -> None:
        unoptimized = self.score("goto loc_100000e40;", "x64_O0")
        self.assertEqual(unoptimized["counts"]["gotos"], 1)
        self.assertIn("gotos", unoptimized["failing"])
        optimized = self.score("goto loc_100000e40;", "x64_O2")
        self.assertEqual(optimized["counts"]["gotos"], 1)
        self.assertNotIn("gotos", optimized["failing"])
        self.assertEqual(optimized["status"], "pass")

    def test_a_clean_rendering_passes_every_predicate(self) -> None:
        clean = """uint64_t sym__sum(uint8_t *data, uint64_t len)
{
    uint64_t total = 0;
    for (uint64_t i = 0; i < len; i++) {
        total = total + data[i];
    }
    return total;
}
"""
        scored = self.score(clean)
        self.assertEqual(scored["status"], "pass", scored)
        self.assertEqual(sum(scored["counts"].values()), 0, scored)


if __name__ == "__main__":
    unittest.main()
