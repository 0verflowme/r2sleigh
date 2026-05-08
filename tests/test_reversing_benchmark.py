from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK_PATH = ROOT / "scripts" / "reversing_benchmark.py"
SPEC = importlib.util.spec_from_file_location("reversing_benchmark", BENCHMARK_PATH)
assert SPEC is not None and SPEC.loader is not None
benchmark = importlib.util.module_from_spec(SPEC)
sys.modules["reversing_benchmark"] = benchmark
SPEC.loader.exec_module(benchmark)


def cmd_result(stdout: str, returncode: int = 0, stderr: str = ""):
    return benchmark.CmdResult(
        returncode=returncode,
        stdout=stdout,
        stderr=stderr,
        elapsed_s=0.001,
    )


DISCOVERY = json.dumps(
    [
        {"name": "sym.small", "offset": 0x1000, "size": 8, "nbbs": 1},
        {"name": "sym.large_worker", "addr": 0x2000, "size": 256, "nbbs": 8},
        {"name": "sym.check_secret", "offset": 0x3000, "size": 96, "nbbs": 4},
    ]
)


class ReversingBenchmarkTests(unittest.TestCase):
    def test_parse_json_payload_skips_non_json_prefix(self):
        output = "INFO: ignored {not json}\n[{\"ok\": true}]\nWARN: trailing text\n"
        self.assertEqual(benchmark.parse_json_payload(output), [{"ok": True}])

    def test_choose_targets_prefers_requested_function(self):
        functions = [
            {"name": "sym.small", "addr": 0x1000, "size": 8, "blocks": 1},
            {"name": "sym.check_secret", "addr": 0x3000, "size": 96, "blocks": 4},
        ]
        selected = benchmark.choose_targets(functions, ("check_secret",), 1)

        self.assertEqual(len(selected), 1)
        self.assertTrue(selected[0]["found"])
        self.assertEqual(selected[0]["addr"], 0x3000)

    def test_choose_targets_uses_largest_functions_when_no_request(self):
        functions = [
            {"name": "sym.small", "addr": 0x1000, "size": 8, "blocks": 1},
            {"name": "sym.large_worker", "addr": 0x2000, "size": 256, "blocks": 8},
            {"name": "sym.mid", "addr": 0x3000, "size": 64, "blocks": 3},
        ]
        selected = benchmark.choose_targets(functions, (), 2)

        self.assertEqual([item["name"] for item in selected], ["sym.large_worker", "sym.mid"])

    def test_run_case_scores_clean_outputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            responses = iter(
                [
                    cmd_result(DISCOVERY),
                    cmd_result('{"name":"sym.check_secret","ops":[]}\n'),
                    cmd_result(DISCOVERY),
                    cmd_result("int check_secret(void) {\n  return 1;\n}\n"),
                    cmd_result("int check_secret(void) {\n  return 1;\n}\n"),
                    cmd_result('{"ret_type":"int","params":[],"mutation_plan":{"mutations":[]}}\n'),
                    cmd_result('{"count":1,"decompile_cache":{"hits":0,"misses":1}}\n'),
                ]
            )

            def runner(r2, path, cmd, timeout, env):
                return next(responses)

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=("check_secret",),
                max_functions=4,
            )
            result = benchmark.run_case(
                "r2",
                case,
                30,
                1,
                False,
                {},
                runner=runner,
            )

        self.assertEqual(result["score"], 100)
        self.assertEqual(result["failures"], [])
        self.assertEqual(result["targets"][0]["commands"]["types"]["json_kind"], "dict")
        self.assertEqual(
            result["targets"][0]["commands"]["decompile_sla"]["decompile_quality"]["classification"],
            "structured",
        )

    def test_run_case_reports_fallback_and_bad_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            responses = iter(
                [
                    cmd_result(DISCOVERY),
                    cmd_result('{"name":"sym.check_secret","ops":[]}\n'),
                    cmd_result(DISCOVERY),
                    cmd_result("/* r2dec fallback: skipped decompilation */\n"),
                    cmd_result(""),
                    cmd_result("not json\n"),
                    cmd_result("{}\n"),
                ]
            )

            def runner(r2, path, cmd, timeout, env):
                return next(responses)

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=("check_secret",),
                max_functions=4,
            )
            result = benchmark.run_case(
                "r2",
                case,
                30,
                1,
                False,
                {},
                runner=runner,
            )

        failure_kinds = {failure["kind"] for failure in result["failures"]}
        self.assertIn("decompiler_fallback", failure_kinds)
        self.assertIn("empty_decompile", failure_kinds)
        self.assertIn("json_parse", failure_kinds)
        self.assertLess(result["score"], 100)

    def test_run_case_classifies_native_discovery_as_radare2_candidate(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            responses = iter(
                [
                    cmd_result("[]\n"),
                    cmd_result(DISCOVERY),
                    cmd_result("int check_secret(void) {\n  return 1;\n}\n"),
                    cmd_result("int check_secret(void) {\n  return 1;\n}\n"),
                    cmd_result('{"ret_type":"int","params":[],"mutation_plan":{"mutations":[]}}\n'),
                    cmd_result('{"count":1,"decompile_cache":{"hits":0,"misses":1}}\n'),
                ]
            )

            def runner(r2, path, cmd, timeout, env):
                return next(responses)

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=("check_secret",),
                max_functions=4,
            )
            result = benchmark.run_case(
                "r2",
                case,
                30,
                1,
                False,
                {},
                runner=runner,
            )

        self.assertIn("radare2_candidate", {failure["kind"] for failure in result["failures"]})
        self.assertEqual(result["native_discovery"]["function_count"], 0)

    def test_quality_metrics_count_temp_and_generic_types(self):
        quality = benchmark.decompile_quality("int f(void) {\n  return tmp:_1 + X29_1;\n}\n")
        type_metrics = benchmark.generic_type_metrics(
            {
                "ret_type": "undefined",
                "params": [{"name": "arg1", "type": "void *"}, {"name": "len", "type": "size_t"}],
            }
        )

        self.assertEqual(quality["classification"], "structured")
        self.assertEqual(quality["artifact_count"], 2)
        self.assertEqual(type_metrics["generic_arg_count"], 1)
        self.assertEqual(type_metrics["generic_type_count"], 2)

    def test_budget_refusal_is_residual_not_hard_fallback(self):
        quality = benchmark.decompile_quality(
            "/* r2dec budget: skipped decompilation for main (2198 blocks > limit 200). */"
        )

        self.assertEqual(quality["classification"], "residual")
        self.assertIsNone(quality["fallback_marker"])
        self.assertGreater(quality["residual_markers"], 0)

    def test_aggregate_is_sorted_and_scores_cases(self):
        cases = [
            {
                "name": "b",
                "corpus": "unit",
                "score": 90,
                "failures": [{"kind": "z"}],
                "targets": [],
            },
            {
                "name": "a",
                "corpus": "unit",
                "score": 100,
                "failures": [{"kind": "a"}],
                "targets": [],
            },
        ]
        summary = benchmark.aggregate(cases)

        self.assertEqual(summary["average_score"], 95.0)
        self.assertEqual(list(summary["failures_by_kind"].keys()), ["a", "z"])


if __name__ == "__main__":
    unittest.main()
