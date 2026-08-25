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

        self.assertIn("long dec_fnv1a32(long arg0, long arg1)", repaired)
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
                [0xAA, 0xBB, 0xCC],
            ],
        ) as json_stdout:
            mapped, blobs, records = verifier.map_image_data(source, Path("unused"))

        self.assertEqual(json_stdout.call_count, 2)
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
        for stage in ("raw", "diagnostic", "differential"):
            self.assertEqual(entry[stage]["status"], "blocked_generation")


if __name__ == "__main__":
    unittest.main()
