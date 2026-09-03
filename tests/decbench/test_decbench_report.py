#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name: str):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


report = load("report_decbench")
merger = load("merge_decbench")


def payload(project: str, score: float | None, decompiled: bool = True) -> dict:
    values = {"r2sleigh": {"byte_match": score}} if score is not None else {}
    return {
        "schema_version": 2,
        "decompilers": ["r2sleigh"],
        "decompiler_versions": {"r2sleigh": "test"},
        "metrics": ["byte_match"],
        "groups": [
            {
                "project": project,
                "binary": "same-name",
                "opt_level": "O0",
                "functions": [
                    {
                        "function": "same_function",
                        "values": values,
                        "decompiled": {"r2sleigh": decompiled},
                    }
                ],
            }
        ],
    }


class ReportTests(unittest.TestCase):
    def test_project_is_part_of_function_key(self) -> None:
        merged = merger.merge([payload("one", 0.5), payload("two", 0.75)])
        rows = report.collect(merged).rows
        self.assertEqual(
            set(rows),
            {
                "one/same-name/O0::same_function",
                "two/same-name/O0::same_function",
            },
        )

    def test_all_function_mean_scores_refusal_as_zero(self) -> None:
        rows = {
            "one/bin/O0::yes": {
                "decompiled": True,
                "scores": {"byte_match": 0.5, "ged": 3.0},
                "reference_decompiled": False,
                "reference": {},
            },
            "one/bin/O0::no": {
                "decompiled": False,
                "scores": {},
                "reference_decompiled": False,
                "reference": {},
            },
        }
        summary = report.summarise(rows)["metrics"]
        self.assertEqual(
            summary["byte_match"]["rendered"], {"n": 1, "mean": 0.5}
        )
        self.assertEqual(summary["byte_match"]["all_functions"]["mean"], 0.25)
        self.assertEqual(summary["ged"]["rendered"], {"n": 1, "mean": 3.0})
        self.assertEqual(summary["ged"]["all_functions"]["mean"], 0.125)

    def test_cached_reference_defines_refused_function_universe(self) -> None:
        current = report.collect(payload("one", 0.5))
        baseline = {
            "functions": {
                "one/same-name/O0::same_function": {
                    "decompiled": True,
                    "scores": {"byte_match": 0.4},
                    "reference_decompiled": True,
                    "reference": {"byte_match": 0.8},
                },
                "one/same-name/O0::refused": {
                    "decompiled": False,
                    "scores": {},
                    "reference_decompiled": True,
                    "reference": {"byte_match": 0.6},
                },
            }
        }
        rows, fill = report.reference_universe(current, baseline)
        self.assertEqual(len(rows), 2)
        self.assertEqual(len(fill["absent"]), 1)
        self.assertFalse(rows["one/same-name/O0::refused"]["decompiled"])
        self.assertEqual(
            report.summarise(rows)["metrics"]["byte_match"]["all_functions"][
                "mean"
            ],
            0.25,
        )

    def test_fresh_reference_does_not_import_old_only_functions(self) -> None:
        current = report.collect(payload("one", 0.5))
        current.reference_version = "new"
        current.reference_cells = {"one/O0"}
        baseline = {
            "functions": {
                "one/same-name/O0::old_only": {
                    "decompiled": False,
                    "scores": {},
                    "reference_decompiled": True,
                    "reference": {"byte_match": 0.9},
                }
            }
        }
        rows, fill = report.reference_universe(current, baseline)
        self.assertEqual(set(rows), {"one/same-name/O0::same_function"})
        self.assertEqual(fill["absent"], [])

    def test_partial_fresh_reference_only_fills_cached_cells(self) -> None:
        fresh = payload("fresh", 0.5)
        fresh["decompilers"].append("angr")
        fresh["decompiler_versions"] = {"angr": "9.3.3"}
        cached = payload("cached", 0.5)
        current = report.collect(merger.merge([fresh, cached]))
        baseline = {
            "functions": {
                "fresh/same-name/O0::old_only": {
                    "decompiled": False,
                    "scores": {},
                    "reference_decompiled": True,
                    "reference": {"byte_match": 0.9},
                },
                "cached/same-name/O0::old_only": {
                    "decompiled": False,
                    "scores": {},
                    "reference_decompiled": True,
                    "reference": {"byte_match": 0.8},
                },
            }
        }
        rows, fill = report.reference_universe(current, baseline)
        self.assertNotIn("fresh/same-name/O0::old_only", rows)
        self.assertIn("cached/same-name/O0::old_only", rows)
        self.assertEqual(
            current.reference_cells,
            {"fresh/O0"},
        )
        self.assertEqual(fill["absent"], ["cached/same-name/O0::old_only"])

    def test_merge_rejects_silent_missing_cell(self) -> None:
        with self.assertRaisesRegex(ValueError, "missing project/opt cells: one/O1"):
            merger.merge([payload("one", 0.5)], {"one/O0", "one/O1"})

    def test_merge_rejects_duplicate_binary_group(self) -> None:
        with self.assertRaisesRegex(ValueError, "duplicate binary group"):
            merger.merge([payload("one", 0.5), payload("one", 0.6)])

    def test_baseline_records_metric_completeness_per_reference_cell(self) -> None:
        old = {
            "reference": {"decompiler": "angr", "version": "9.3.3"},
            "selection": {"cells": ["cached/O0"]},
            "groups": [],
            "functions": {},
            "summary": {"metrics": {"byte_match": {}}},
        }
        fresh_payload = payload("fresh", 0.5)
        fresh_payload["decompilers"].append("angr")
        fresh_payload["decompiler_versions"] = {"angr": "9.3.3"}
        fresh_payload["metrics"] = ["byte_match", "vj_ged"]
        current = report.collect(merger.merge([fresh_payload]))
        measured = report.measured_record(current, current.rows)
        baseline = report.merge_baseline(old, measured)
        self.assertEqual(
            baseline["reference"]["metric_cells"],
            {
                "byte_match": ["cached/O0", "fresh/O0"],
                "vj_ged": ["fresh/O0"],
            },
        )
        self.assertEqual(
            baseline["selection"]["cells"],
            ["cached/O0", "fresh/O0"],
        )


if __name__ == "__main__":
    unittest.main()
