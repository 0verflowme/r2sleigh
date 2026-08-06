from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock
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


def batched_stdout(entries):
    lines = []
    for name, repeat_idx, payload in entries:
        lines.append(benchmark.batched_section_start(name, repeat_idx))
        lines.extend(str(payload).splitlines())
        lines.append(benchmark.batched_section_end(name, repeat_idx))
    return "\n".join(lines)


class ReversingBenchmarkTests(unittest.TestCase):
    def test_checked_in_source_oracle_does_not_bless_synthetic_summary_c(self):
        oracle_path = ROOT / "tests" / "gold" / "source_oracle.json"
        oracle = json.loads(oracle_path.read_text())
        synthetic_markers = (
            "summary locals are synthetic",
            "summary_value",
            "summary_count",
            "summary_hash",
            "summary_i",
            "summary_byte",
            "return summary_",
        )
        offenders = []
        for expectation in oracle.get("expectations", []):
            for needle in expectation.get("contains", []):
                if any(marker in needle for marker in synthetic_markers):
                    offenders.append((expectation.get("id"), needle))

        self.assertEqual([], offenders)

    def test_parse_json_payload_skips_non_json_prefix(self):
        output = "INFO: ignored {not json}\n[{\"ok\": true}]\nWARN: trailing text\n"
        self.assertEqual(benchmark.parse_json_payload(output), [{"ok": True}])

    def test_run_r2_preserves_timeout_partial_byte_output(self):
        exc = benchmark.subprocess.TimeoutExpired(
            ["r2"],
            timeout=1,
            output=b"partial stdout\n",
            stderr=b"partial stderr\n",
        )
        with mock.patch.object(benchmark.subprocess, "run", side_effect=exc):
            result = benchmark.run_r2("r2", Path("/tmp/sample"), "aaa", 1, {})

        self.assertEqual(result.returncode, 124)
        self.assertEqual(result.stdout, "partial stdout\n")
        self.assertEqual(result.stderr, "partial stderr\n")

    def test_choose_targets_prefers_requested_function(self):
        functions = [
            {"name": "sym.small", "addr": 0x1000, "size": 8, "blocks": 1},
            {"name": "sym.check_secret", "addr": 0x3000, "size": 96, "blocks": 4},
        ]
        selected = benchmark.choose_targets(functions, ("check_secret",), 1)

        self.assertEqual(len(selected), 1)
        self.assertTrue(selected[0]["found"])
        self.assertEqual(selected[0]["addr"], 0x3000)

    def test_choose_targets_prefers_exact_debug_alias_before_symbol_alias(self):
        functions = [
            {"name": "sym.worker", "addr": 0x1000, "size": 96, "blocks": 4},
            {"name": "dbg.worker", "addr": 0x2000, "size": 96, "blocks": 4},
        ]

        selected = benchmark.choose_targets(functions, ("dbg.worker",), 1)

        self.assertEqual(selected[0]["name"], "dbg.worker")
        self.assertEqual(selected[0]["target_match"], "exact")
        self.assertNotIn("target_alias", selected[0])

    def test_choose_targets_classifies_missing_debug_alias_without_losing_target(self):
        functions = [
            {"name": "sym.xstrtoumax", "addr": 0x1000, "size": 96, "blocks": 4},
        ]

        selected = benchmark.choose_targets(functions, ("dbg.xstrtoumax",), 1)
        failures = benchmark.collect_failures(
            {
                "discovery": {"returncode": 0, "function_count": 1},
                "targets": selected,
            }
        )

        self.assertTrue(selected[0]["found"])
        self.assertEqual(selected[0]["target_match"], "symbol_debug_alias")
        self.assertEqual(
            selected[0]["target_alias"],
            {
                "kind": "missing_debug_target_alias",
                "requested": "dbg.xstrtoumax",
                "matched": "sym.xstrtoumax",
                "requested_prefix": "dbg",
                "matched_prefix": "sym",
            },
        )
        self.assertEqual(
            failures,
            [
                {
                    "kind": "missing_debug_target_alias",
                    "target": "dbg.xstrtoumax",
                    "matched": "sym.xstrtoumax",
                    "requested_prefix": "dbg",
                    "matched_prefix": "sym",
                }
            ],
        )

    def test_choose_targets_classifies_missing_symbol_alias_without_losing_target(self):
        functions = [
            {"name": "dbg.printf_fetchargs", "addr": 0x1000, "size": 96, "blocks": 4},
        ]

        selected = benchmark.choose_targets(functions, ("sym.printf_fetchargs",), 1)

        self.assertTrue(selected[0]["found"])
        self.assertEqual(selected[0]["target_alias"]["kind"], "missing_symbol_target_alias")

    def test_choose_targets_uses_largest_functions_when_no_request(self):
        functions = [
            {"name": "sym.small", "addr": 0x1000, "size": 8, "blocks": 1},
            {"name": "sym.large_worker", "addr": 0x2000, "size": 256, "blocks": 8},
            {"name": "sym.mid", "addr": 0x3000, "size": 64, "blocks": 3},
        ]
        selected = benchmark.choose_targets(functions, (), 2)

        self.assertEqual([item["name"] for item in selected], ["sym.large_worker", "sym.mid"])

    def test_choose_targets_skips_import_boilerplate_and_anonymous_samples(self):
        functions = [
            {"name": "sym.imp.free", "addr": 0x1000, "size": 4096, "blocks": 3},
            {"name": "fcn.00000000", "addr": 0, "size": 8192, "blocks": 8},
            {"name": "fcn.00002000", "addr": 0x2000, "size": 2048, "blocks": 6},
            {"name": "sym._fini", "addr": 0x3000, "size": 1024, "blocks": 2},
            {"name": "dbg.real_worker", "addr": 0x4000, "size": 64, "blocks": 4},
        ]
        selected = benchmark.choose_targets(functions, (), 2)

        self.assertEqual([item["name"] for item in selected], ["dbg.real_worker"])

    def test_choose_targets_keeps_explicit_import_requests(self):
        functions = [
            {"name": "sym.imp.free", "addr": 0x1000, "size": 8, "blocks": 1},
        ]
        selected = benchmark.choose_targets(functions, ("sym.imp.free",), 1)

        self.assertEqual(selected[0]["name"], "sym.imp.free")
        self.assertEqual(selected[0]["target_match"], "exact")

    def test_choose_targets_returns_empty_when_only_unsampleable_code_exists(self):
        functions = [
            {"name": "sym.imp.free", "addr": 0x1000, "size": 4096, "blocks": 3},
            {"name": "fcn.00000000", "addr": 0, "size": 8192, "blocks": 8},
            {"name": "sym._fini", "addr": 0x3000, "size": 1024, "blocks": 2},
        ]
        selected = benchmark.choose_targets(functions, (), 4)

        self.assertEqual(selected, [])

    def test_focused_coreutils_cases_pin_hot_targets(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("dd", "printf", "uniq"):
                path = root / name
                path.write_bytes(b"\x00")
                path.chmod(path.stat().st_mode | 0o111)

            cases = benchmark.focused_coreutils_cases(str(root), "aaa", 12)

        self.assertEqual([case.name for case in cases], ["dd", "printf", "uniq"])
        self.assertEqual(
            [case.targets for case in cases],
            [
                ("dbg.xstrtoumax",),
                ("sym.printf_fetchargs",),
                ("dbg.readlinebuffer_delim",),
            ],
        )
        self.assertTrue(all(case.max_functions == 12 for case in cases))

    def test_target_family_buckets_hot_coreutils_workers(self):
        self.assertEqual(benchmark.target_family("sym.oputs_.constprop.0"), "record_stream")
        self.assertEqual(benchmark.target_family("dbg.cut_fields_bytesearch"), "record_stream")
        self.assertEqual(
            benchmark.target_family("sym.__strftime_internal.isra.0"),
            "format_render",
        )
        self.assertEqual(benchmark.target_family("dbg.fdfile_has_aclinfo"), "metadata_traversal")
        self.assertEqual(benchmark.target_family("dbg.mergefps"), "sort_merge")
        self.assertEqual(benchmark.target_family("dbg.copy"), "file_copy")
        self.assertEqual(benchmark.target_family("sym.rpl_fts_read"), "fts")
        self.assertEqual(benchmark.target_family("dbg.main"), "main")
        self.assertEqual(benchmark.target_family("dbg.write_counts"), "counter_output")
        self.assertEqual(benchmark.target_family("dbg.verror_at_line"), "diagnostic_wrapper")
        self.assertEqual(benchmark.target_family("sym.argmatch"), "argmatch")
        self.assertEqual(benchmark.target_family("dbg.__xargmatch_internal"), "argmatch")
        self.assertEqual(benchmark.target_family("sym.quotearg_alloc_mem"), "quote_options")
        self.assertEqual(benchmark.target_family("sym.quote_name_buf.constprop.0"), "quote_options")
        self.assertEqual(benchmark.target_family("dbg.cut_file"), "record_stream")
        self.assertEqual(benchmark.target_family("dbg.memchr2"), "record_stream")
        self.assertEqual(benchmark.target_family("sym.hash_insert_if_absent"), "hash_table")
        self.assertEqual(benchmark.target_family("dbg.wc_lines_avx512"), "vector_scan")
        self.assertEqual(benchmark.target_family("sym.version_etc_va"), "format_render")
        self.assertEqual(benchmark.target_family("dbg.renameatu"), "metadata_traversal")
        self.assertEqual(benchmark.target_family("sym.xpalloc"), "allocation")
        self.assertEqual(benchmark.target_family("dbg.sort_files"), "sort_merge")
        self.assertEqual(benchmark.target_family("dbg.stream_open"), "libc_wrapper")
        self.assertEqual(benchmark.target_family("dbg.same_nameat"), "metadata_traversal")
        self.assertEqual(benchmark.target_family("sym.mcel_scan"), "multibyte")
        self.assertEqual(benchmark.target_family("dbg.strmode"), "format_render")
        self.assertEqual(benchmark.target_family("dbg.do_statx"), "metadata_traversal")
        self.assertEqual(benchmark.target_family("dbg.mfile_name_concat"), "path_alloc")
        self.assertEqual(benchmark.target_family("dbg.getuidbyname"), "metadata_traversal")
        self.assertEqual(benchmark.target_family("dbg.init_node"), "sort_merge")
        self.assertEqual(benchmark.target_family("sym.mcel_scant"), "multibyte")
        self.assertEqual(benchmark.target_family("dbg.filenvercmp"), "version_compare")
        self.assertEqual(
            benchmark.target_family("sym.print_file_name_and_frills.isra.0"),
            "format_render",
        )
        self.assertEqual(benchmark.target_family("dbg.try_tempname_len"), "tempname")
        self.assertEqual(benchmark.target_family("dbg.close_stdout"), "libc_wrapper")
        self.assertEqual(benchmark.target_family("dbg.write_bytes"), "record_stream")

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
                    cmd_result('{"count":1}\n'),
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
        self.assertEqual(len(result["targets"][0]["command_events"]), 4)
        self.assertFalse(result["targets"][0]["commands"]["types"]["event"]["timeout"])
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

    def test_collect_failures_reports_timeout_without_cascading_noise(self):
        failures = benchmark.collect_failures(
            {
                "discovery": {"returncode": 0, "function_count": 1},
                "targets": [
                    {
                        "name": "sym.hot",
                        "commands": {
                            "decompile_sla": {
                                "returncode": 124,
                                "timeout": True,
                                "empty": True,
                                "json_error": "empty output",
                            }
                        },
                    }
                ]
            }
        )

        self.assertEqual(
            failures,
            [{"kind": "timeout", "target": "sym.hot", "command": "decompile_sla"}],
        )

    def test_collect_failures_gates_manual_decompiler_failures(self):
        quality = benchmark.decompile_quality(
            "int f(int a) {\n"
            "  while (a) { break; }\n"
            "  do { } while (a);\n"
            "  fcn.401000(arg1);\n"
            "  tmp:_2 = stack_8;\n"
            "}\n"
        )
        comment_only = benchmark.decompile_quality("/* summary: no statements recovered */\n")
        case_result = {
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [
                {
                    "name": "sym.hot",
                    "commands": {
                        "types": {
                            "returncode": 0,
                            "type_metrics": {
                                "ret_type": "void",
                                "param_count": 2,
                            },
                        },
                        "decompile_sla": {
                            "returncode": 0,
                            "timeout": False,
                            "decompile_quality": quality,
                        },
                        "decompile_pdd": {
                            "returncode": 0,
                            "timeout": False,
                            "decompile_quality": comment_only,
                        },
                    },
                }
            ],
        }

        failures = benchmark.collect_failures(case_result)
        kinds = {failure["kind"] for failure in failures}
        case_result["failures"] = failures

        self.assertTrue(
            {
                "argn_leak",
                "comment_only_decompile",
                "decompile_header_return_mismatch",
                "decompile_header_signature_mismatch",
                "empty_loop_body",
                "fake_stack_slot",
                "fake_while_break_wrapper",
                "missing_return_nonvoid",
                "unresolved_fcn_or_temp_stack_leak",
            }.issubset(kinds)
        )
        self.assertLessEqual(benchmark.score_case(case_result), 34)

    def test_gold_oracle_gates_source_expectations(self):
        case = benchmark.BinaryCase(
            name="vuln_test_x86",
            path=Path("/tmp/vuln_test_x86"),
            corpus="repo-fixtures",
            analysis="aaa",
            targets=("test_struct_array_index",),
            max_functions=1,
        )
        target = {
            "name": "sym.test_struct_array_index",
            "requested": "test_struct_array_index",
        }
        gold = [
            {
                "id": "struct-array-index",
                "corpus": "repo-fixtures",
                "case": "vuln_test_x86",
                "target": "test_struct_array_index",
                "command": "decompile_sla",
                "owner": "r2types",
                "contains": ["DemoStruct*", "arr[idx].third"],
                "not_contains": ["sla_struct_", "*(arr +"],
            }
        ]
        entry = benchmark.command_summary(
            "decompile_sla",
            cmd_result(
                "int32_t test_struct_array_index(struct sla_struct_bad* arr, int32_t idx)\n"
                "{\n"
                "    *(arr + idx * 56 + 8) = 1;\n"
                "}\n"
            ),
            False,
            case=case,
            target=target,
            gold_manifest=gold,
        )
        case_result = {
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [{"name": target["name"], "commands": {"decompile_sla": entry}}],
        }

        failures = benchmark.collect_failures(case_result)
        kinds = [failure["kind"] for failure in failures]

        self.assertEqual(entry["gold_oracle"]["status"], "failed")
        self.assertIn("source_oracle_failure", kinds)
        self.assertTrue(any(failure.get("owner") == "r2types" for failure in failures))
        case_result["failures"] = failures
        self.assertLess(benchmark.score_case(case_result), 100)

    def test_gold_oracle_passes_expected_source_shape(self):
        case = benchmark.BinaryCase(
            name="vuln_test_x86",
            path=Path("/tmp/vuln_test_x86"),
            corpus="repo-fixtures",
            analysis="aaa",
            targets=("test_struct_array_index",),
            max_functions=1,
        )
        target = {"name": "sym.test_struct_array_index"}
        gold = [
            {
                "target": "dbg.test_struct_array_index",
                "command": "decompile_sla",
                "owner": "r2types",
                "contains": ["DemoStruct*", "arr[idx].fourteenth + arr[idx].third"],
                "not_contains": ["sla_struct_", "*(arr +"],
            }
        ]
        entry = benchmark.command_summary(
            "decompile_sla",
            cmd_result(
                "int32_t test_struct_array_index(DemoStruct* arr, int32_t idx, int32_t v)\n"
                "{\n"
                "    arr[idx].third = v;\n"
                "    return arr[idx].fourteenth + arr[idx].third;\n"
                "}\n"
            ),
            False,
            case=case,
            target=target,
            gold_manifest=gold,
        )

        self.assertEqual(entry["gold_oracle"]["status"], "ok")
        self.assertEqual(entry["gold_oracle"]["expectation_count"], 1)
        self.assertEqual(entry["gold_oracle"]["failures"], [])

    def test_load_gold_manifest_requires_canonical_owner(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "gold.json"
            path.write_text(
                json.dumps(
                    {
                        "expectations": [
                            {
                                "target": "dbg.worker",
                                "command": "decompile_sla",
                                "contains": ["return 1;"],
                            }
                        ]
                    }
                )
            )

            with self.assertRaisesRegex(ValueError, "canonical owner"):
                benchmark.load_gold_manifest(path)

            path.write_text(
                json.dumps(
                    {
                        "expectations": [
                            {
                                "target": "dbg.worker",
                                "command": "decompile_sla",
                                "owner": "r2dec",
                                "contains": ["return 1;"],
                            }
                        ]
                    }
                )
            )

            expectations = benchmark.load_gold_manifest(path)

        self.assertEqual(expectations[0]["owner"], "r2dec")

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
                    cmd_result('{"count":1}\n'),
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
        quality = benchmark.decompile_quality(
            "int f(int len) {\n  int len;\n  return tmp:_1 + X29_1 + &local_1;\n}\n"
        )
        type_metrics = benchmark.generic_type_metrics(
            {
                "ret_type": "undefined",
                "params": [{"name": "arg1", "type": "void *"}, {"name": "len", "type": "size_t"}],
            }
        )

        self.assertEqual(quality["classification"], "structured")
        self.assertEqual(quality["artifact_count"], 2)
        self.assertEqual(quality["address_of_scalar_count"], 1)
        self.assertEqual(quality["local_stack_placeholder_count"], 1)
        self.assertEqual(quality["stack_address_leak_count"], 1)
        self.assertEqual(quality["raw_temp_stack_leak_count"], 2)
        self.assertEqual(quality["fake_stack_slot_count"], 1)
        self.assertEqual(quality["shadowed_param_count"], 1)
        self.assertEqual(quality["readability_smell_count"], 4)
        self.assertEqual(quality["source_smell_count"], 3)
        self.assertEqual(type_metrics["generic_arg_count"], 1)
        self.assertEqual(type_metrics["generic_type_count"], 2)

    def test_quality_metrics_do_not_count_source_grade_fixed_width_types_as_generic(self):
        type_metrics = benchmark.generic_type_metrics(
            {
                "ret_type": "int32_t",
                "params": [
                    {"name": "hash", "type": "uint64_t"},
                    {"name": "buf", "type": "uint8_t *"},
                ],
            }
        )

        self.assertEqual(type_metrics["generic_arg_count"], 0)
        self.assertEqual(type_metrics["generic_type_count"], 0)

    def test_quality_metrics_count_readability_noise(self):
        quality = benchmark.decompile_quality(
            "int f(void) {\n"
            "  goto done;\n"
            "  return call_401000((void *)arg) + (int)x + (char *)&var_8h + sla_struct_tmp;\n"
            "done:\n"
            "  return 0;\n"
            "}\n"
        )

        self.assertEqual(quality["classification"], "structured")
        self.assertEqual(quality["cast_expr_count"], 3)
        self.assertEqual(quality["pointer_cast_count"], 2)
        self.assertEqual(quality["stack_address_leak_count"], 1)
        self.assertEqual(quality["raw_temp_stack_leak_count"], 1)
        self.assertEqual(quality["fake_stack_slot_count"], 1)
        self.assertEqual(quality["control_flow_noise_count"], 1)
        self.assertEqual(quality["call_readability_noise_count"], 1)
        self.assertEqual(quality["synthetic_type_leak_count"], 1)
        self.assertEqual(quality["readability_smell_count"], 11)

    def test_quality_metrics_count_manual_failure_patterns(self):
        quality = benchmark.decompile_quality(
            "int f(int a) {\n"
            "  while (a) { break; }\n"
            "  do { } while (a);\n"
            "  fcn.401000(arg1);\n"
            "  tmp:_2 = stack_8;\n"
            "  compute_numeric_transform(accumulator);\n"
            "  RCX = edx_1;\n"
            "}\n"
        )
        comment_only = benchmark.decompile_quality("/* summary: no statements recovered */\n")

        self.assertEqual(quality["header_ret_type"], "int")
        self.assertEqual(quality["header_param_count"], 1)
        self.assertTrue(quality["missing_return_nonvoid"])
        self.assertEqual(quality["fake_while_break_wrapper_count"], 1)
        self.assertEqual(quality["empty_loop_body_count"], 1)
        self.assertEqual(quality["argn_leak_count"], 1)
        self.assertEqual(quality["summary_pseudo_call_count"], 1)
        self.assertGreaterEqual(quality["raw_register_artifact_count"], 1)
        self.assertEqual(quality["unresolved_fcn_count"], 1)
        self.assertGreaterEqual(quality["raw_temp_stack_leak_count"], 2)
        self.assertEqual(quality["fake_stack_slot_count"], 1)
        self.assertTrue(comment_only["comment_only"])
        self.assertFalse(comment_only["missing_return_nonvoid"])

    def test_quality_metrics_count_broader_fake_semantics_patterns(self):
        quality = benchmark.decompile_quality(
            "unknown_t bad(undefined1 arg1) {\n"
            "  switch (arg1) { case fake_case: break; }\n"
            "  helper(fake_arg, tmp:_1);\n"
            "}\n"
        )

        self.assertEqual(quality["fake_switch_case_count"], 1)
        self.assertEqual(quality["fake_call_arg_count"], 1)
        self.assertGreaterEqual(quality["fake_signature_count"], 1)

    def test_quality_metrics_count_proof_coverage_gap_comments(self):
        quality = benchmark.decompile_quality(
            "int f(void) {\n"
            "  /* r2dec residual: certified render contract failed: rendered 1 call expression(s) with only 0 CallsiteCertificate(s) */\n"
            "  /* engine render permission residual: missing expression proof */\n"
            "}\n"
        )

        self.assertGreaterEqual(quality["proof_coverage_gap_count"], 2)
        self.assertGreaterEqual(quality["readability_smell_count"], 2)

    def test_quality_metrics_do_not_treat_explicit_summary_return_refusal_as_fake_missing_return(self):
        quality = benchmark.decompile_quality(
            "int f(void) {\n"
            "  /* summary return unresolved; value intentionally not reconstructed */\n"
            "}\n"
        )

        self.assertTrue(quality["explicit_unresolved_summary_return"])
        self.assertFalse(quality["missing_return_nonvoid"])
        self.assertEqual(quality["undefined_identifier_return_count"], 0)

    def test_quality_metrics_count_undefined_summary_placeholder_return(self):
        quality = benchmark.decompile_quality(
            "uint64_t fnv_fold(uint8_t* buf, size_t n)\n"
            "{\n"
            "  /* worker summary: hash_fold: mem=buf len=n fold=xor/fnv1a_hash:64 */\n"
            "  return fnv1a_hash;\n"
            "}\n"
        )

        self.assertEqual(quality["undefined_identifier_return_count"], 1)
        self.assertGreaterEqual(quality["readability_smell_count"], 1)

    def test_quality_metrics_accept_compact_pointer_local_return(self):
        quality = benchmark.decompile_quality(
            "int8_t* alloc_and_copy(int8_t* src, size_t len)\n"
            "{\n"
            "  int8_t* buf;\n"
            "  buf = malloc(len + 1);\n"
            "  return buf;\n"
            "}\n"
        )

        self.assertEqual(quality["undefined_identifier_return_count"], 0)

    def test_quality_metrics_count_unmarked_source_like_summary_locals(self):
        quality = benchmark.decompile_quality(
            "uint64_t fnv_fold(uint8_t* buf, size_t n)\n"
            "{\n"
            "  /* semantic role: numeric_transform; source=Structural; confidence=Likely */\n"
            "  /* summary projection: hash_fold loop */\n"
            "  uint64_t hash = 0;\n"
            "  for (size_t i = 0; i < n; i++) {\n"
            "    unsigned char c = buf[i];\n"
            "    hash ^= c;\n"
            "  }\n"
            "  return hash;\n"
            "}\n"
        )

        self.assertEqual(quality["source_like_summary_local_count"], 3)
        self.assertEqual(quality["summary_synthetic_local_count"], 3)
        self.assertEqual(quality["unmarked_summary_synthetic_local_count"], 3)
        self.assertEqual(quality["misleading_summary_role_count"], 1)
        self.assertEqual(quality["name_hint_structured_route_count"], 0)
        self.assertEqual(quality["missing_semantic_claims_count"], 1)
        self.assertEqual(quality["missing_summary_render_contract_count"], 1)
        self.assertEqual(quality["claimless_summary_projection_count"], 0)

    def test_quality_metrics_count_marked_synthetic_summary_locals(self):
        quality = benchmark.decompile_quality(
            "uint64_t fnv_fold(uint8_t* buf, size_t n)\n"
            "{\n"
            "  /* summary role: hash_fold; source=SummaryEvidence; confidence=Likely */\n"
            "  /* render contract: summary projection only; native CFG/control not reconstructed */\n"
            "  /* semantic claims: renderable=1, control=0, memory=0, value=1, summary_roles=1, type_args=2, out_args=0, name_hint=0, residual=0 */\n"
            "  /* summary projection (not native CFG): hash_fold loop */\n"
            "  /* summary locals are synthetic; source local names were not recovered */\n"
            "  uint64_t summary_hash = 0;\n"
            "  for (size_t summary_i = 0; summary_i < n; summary_i++) {\n"
            "    unsigned char summary_byte = buf[summary_i];\n"
            "    summary_hash ^= summary_byte;\n"
            "  }\n"
            "  return summary_hash;\n"
            "}\n"
        )

        self.assertEqual(quality["source_like_summary_local_count"], 3)
        self.assertEqual(quality["summary_synthetic_local_count"], 3)
        self.assertEqual(quality["unmarked_summary_synthetic_local_count"], 0)
        self.assertEqual(quality["misleading_summary_role_count"], 0)
        self.assertEqual(quality["name_hint_structured_route_count"], 0)
        self.assertEqual(quality["missing_semantic_claims_count"], 0)
        self.assertEqual(quality["missing_summary_render_contract_count"], 0)
        self.assertEqual(quality["claimless_summary_projection_count"], 0)
        self.assertEqual(quality["missing_summary_role_certificate_count"], 0)
        self.assertEqual(quality["classification"], "structured")
        self.assertGreaterEqual(quality["readability_smell_count"], 3)
        self.assertEqual(quality["residual_markers"], 0)

    def test_quality_metrics_ignore_zero_residual_semantic_claim(self):
        quality = benchmark.decompile_quality(
            "int f(void)\n"
            "{\n"
            "  /* semantic claims: renderable=1, control=0, memory=0, value=1, summary_roles=1, type_args=0, out_args=0, name_hint=0, residual=0 */\n"
            "  return 0;\n"
            "}\n"
        )

        self.assertEqual(quality["classification"], "structured")
        self.assertEqual(quality["residual_markers"], 0)

    def test_quality_metrics_count_positive_residual_semantic_claim(self):
        quality = benchmark.decompile_quality(
            "int f(void)\n"
            "{\n"
            "  /* semantic claims: renderable=1, control=0, memory=0, value=1, summary_roles=1, type_args=0, out_args=0, name_hint=0, residual=2 */\n"
            "  return 0;\n"
            "}\n"
        )

        self.assertEqual(quality["classification"], "residual")
        self.assertEqual(quality["residual_markers"], 1)

    def test_quality_metrics_count_claimless_summary_projection(self):
        quality = benchmark.decompile_quality(
            "uint64_t fnv_fold(uint8_t* buf, size_t n)\n"
            "{\n"
            "  /* summary role: hash_fold; source=SummaryEvidence; confidence=Likely */\n"
            "  /* render contract: summary projection only; native CFG/control not reconstructed */\n"
            "  /* semantic claims: renderable=0, control=0, memory=0, value=0, summary_roles=0, type_args=0, out_args=0, name_hint=0, residual=0 */\n"
            "  /* summary projection (not native CFG): hash_fold loop */\n"
            "  /* summary locals are synthetic; source local names were not recovered */\n"
            "  uint64_t summary_hash = 0;\n"
            "  return summary_hash;\n"
            "}\n"
        )

        self.assertEqual(quality["missing_semantic_claims_count"], 0)
        self.assertEqual(quality["missing_summary_render_contract_count"], 0)
        self.assertEqual(quality["claimless_summary_projection_count"], 1)
        self.assertEqual(quality["missing_summary_role_certificate_count"], 1)

    def test_quality_metrics_count_name_hint_structured_route(self):
        quality = benchmark.decompile_quality(
            "int f(int x)\n"
            "{\n"
            "  /* summary role hint: parser; source=NameHint; confidence=Heuristic */\n"
            "  for (size_t i = 0; i < 4; i++) {\n"
            "    x++;\n"
            "  }\n"
            "  return x;\n"
            "}\n"
        )

        self.assertEqual(quality["name_hint_structured_route_count"], 1)

    def test_quality_metrics_count_all_summary_pseudo_calls(self):
        quality = benchmark.decompile_quality(
            "void f(void)\n"
            "{\n"
            "  scan_string_summary(arg0, 0);\n"
            "  walk_table_summary(arg1, unknown_terminator);\n"
            "  parse_base10_numeric_summary(arg2);\n"
            "  copy_file_data_summary(src_fd, dest_fd, len);\n"
            "  malloc_summary(size);\n"
            "  free_summary(ptr);\n"
            "  diagnose_summary(fmt);\n"
            "  fetch_printf_arguments(ap, out);\n"
            "  render_formatted_output(fmt);\n"
            "  probe_file_metadata(path);\n"
            "  run_program_orchestrator(argc, argv, envp);\n"
            "  compute_numeric_transform(accumulator);\n"
            "}\n"
        )

        self.assertEqual(quality["summary_pseudo_call_count"], 12)
        self.assertGreaterEqual(quality["readability_smell_count"], 12)

    def test_quality_metrics_count_invalid_control_flow_and_pointer_literal_compare(self):
        quality = benchmark.decompile_quality(
            "int32_t parse_number(int8_t* str)\n"
            "{\n"
            "    if (str != 45) {\n"
            "        break;\n"
            "    }\n"
            "    if (43 == str) {\n"
            "        break;\n"
            "    }\n"
            "}\n"
        )

        self.assertEqual(quality["orphan_break_count"], 2)
        self.assertEqual(quality["pointer_scalar_compare_count"], 2)
        self.assertEqual(quality["readability_smell_count"], 4)

    def test_budget_refusal_is_residual_not_hard_fallback(self):
        quality = benchmark.decompile_quality(
            "/* r2dec budget: skipped decompilation for main (2198 blocks > limit 200). */"
        )

        self.assertEqual(quality["classification"], "residual")
        self.assertIsNone(quality["fallback_marker"])
        self.assertGreater(quality["residual_markers"], 0)

    def test_timeout_inside_identifier_is_not_residual(self):
        quality = benchmark.decompile_quality(
            "void dbg.settimeout(double duration, bool warn)\n"
            "{\n"
            "    /* semantic role: settimeout; source=NameHint */\n"
            "    compute_numeric_transform(duration);\n"
            "}\n"
        )

        self.assertEqual(quality["classification"], "structured")
        self.assertEqual(quality["residual_markers"], 0)

    def test_missing_r2ghidra_message_is_decompiler_fallback(self):
        quality = benchmark.decompile_quality("You need to install the plugin with r2pm -ci r2ghidra\n")

        self.assertEqual(quality["classification"], "fallback")
        self.assertEqual(quality["fallback_marker"], "r2pm -ci r2ghidra")

    def test_parse_batched_sections_extracts_command_payloads(self):
        stdout = "\n".join(
            [
                "ignored prefix",
                benchmark.batched_time_marker("START", "types", 0),
                "1000000000",
                benchmark.batched_section_start("types", 0),
                '{"ret_type":"int"}',
                benchmark.batched_section_end("types", 0),
                benchmark.batched_time_marker("END", "types", 0),
                "1500000000",
                benchmark.batched_section_start("decompile_sla", 0),
                "int f(void) {",
                "  return 1;",
                "}",
                benchmark.batched_section_end("decompile_sla", 0),
            ]
        )

        sections = benchmark.parse_batched_sections(stdout)
        _sections, timings = benchmark.parse_batched_output(stdout)

        self.assertEqual(sections[("types", 0)], '{"ret_type":"int"}\n')
        self.assertEqual(timings[("types", 0)], (1000000000, 1500000000))
        self.assertIn("return 1", sections[("decompile_sla", 0)])

    def test_parse_batched_output_tracks_started_and_completed_sections(self):
        stdout = "\n".join(
            [
                benchmark.batched_section_start("done", 0),
                "ok",
                benchmark.batched_section_end("done", 0),
                benchmark.batched_section_start("partial", 0),
                "still running",
            ]
        )

        sections, _timings, started, completed = benchmark.parse_batched_output_detailed(stdout)

        self.assertEqual(sections[("done", 0)], "ok\n")
        self.assertEqual(sections[("partial", 0)], "still running\n")
        self.assertIn(("done", 0), started)
        self.assertIn(("partial", 0), started)
        self.assertIn(("done", 0), completed)
        self.assertNotIn(("partial", 0), completed)

    def test_run_case_batched_scores_clean_outputs_and_reports_artifact_cache_hits(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            batch_stdout = "\n".join(
                [
                    benchmark.batched_section_start("t0_decompile_sla", 0),
                    "int check_secret(void) {\n  return 1;\n}",
                    benchmark.batched_section_end("t0_decompile_sla", 0),
                    benchmark.batched_section_start("t0_decompile_pdd", 0),
                    "int check_secret(void) {\n  return 1;\n}",
                    benchmark.batched_section_end("t0_decompile_pdd", 0),
                    benchmark.batched_section_start("t0_types", 0),
                    '{"ret_type":"int","params":[],"mutation_plan":{"mutations":[]}}',
                    benchmark.batched_section_end("t0_types", 0),
                    benchmark.batched_section_start("t0_profile", 0),
                    (
                        '{"count":1,'
                        '"engine_cache":{"analysis":{"hits":1,"misses":2,"lookups":3,"insertions":2,"evictions":0},'
                        '"artifacts":{"hits":1,"misses":1,"lookups":2,"insertions":1,"evictions":0},'
                        '"total":{"hits":2,"misses":3,"lookups":5,"insertions":3,"evictions":0}}}'
                    ),
                    benchmark.batched_section_end("t0_profile", 0),
                ]
            )
            responses = iter(
                [
                    cmd_result(DISCOVERY),
                    cmd_result('{"name":"sym.check_secret","ops":[]}\n'),
                    cmd_result(DISCOVERY),
                    cmd_result(batch_stdout),
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
                isolate_commands=False,
            )

        target = result["targets"][0]
        self.assertEqual(result["execution_mode"], "batched")
        self.assertEqual(target["execution_mode"], "batched")
        self.assertIn("setup_event", target)
        self.assertEqual(result["score"], 100)
        self.assertEqual(
            target["commands"]["profile"]["profile_metrics"]["engine_cache"]["total"]["hits"],
            2,
        )
        self.assertEqual(
            target["commands"]["profile"]["profile_metrics"]["engine_cache"]["artifacts"]["hits"],
            1,
        )
        self.assertEqual(
            target["commands"]["decompile_pdd"]["decompile_quality"]["classification"],
            "structured",
        )

    def test_command_summary_exposes_type_summary_fast_path_metrics(self):
        payload = {
            "ret_type": "int",
            "params": [],
            "mutation_plan": {"mutations": []},
            "summary_cache": {
                "hits": 4,
                "misses": 1,
                "lookups": 5,
                "insertions": 1,
                "evictions": 0,
            },
            "interproc": {
                "callsite_count": 3,
                "iterations": 1,
                "max_iterations": 4,
                "converged": True,
                "summary": {"root": "sym.worker"},
            },
            "compiled_semantics": {
                "granularity": "summary_only",
                "execution": "native",
                "slice_class": "record_stream",
                "summary_attempted": 1,
                "summary_budget_exhausted": 0,
                "summary_scc_count": 2,
                "native_worker_summary_count": 2,
                "native_region_summary_count": 1,
            },
            "plans": {
                "type_plan": {"VmSummaryOnly": {"reason": "summary"}},
                "decompile": {"NativeSummaryIslands": {"reason": "summary"}},
            },
            "phase_timings": [
                {"phase": "interproc_summary", "elapsed_us": 10},
                {"phase": "semantic_summary", "elapsed_us": 20},
                {"phase": "semantic_artifact", "elapsed_us": 0},
            ],
        }

        entry = benchmark.command_summary("types", cmd_result(json.dumps(payload)), False)

        self.assertEqual(entry["cache_metrics"]["summary_cache"]["hits"], 4)
        self.assertTrue(entry["fast_path_metrics"]["cache_hit"])
        self.assertTrue(entry["fast_path_metrics"]["summary_fast_path"])
        self.assertTrue(entry["fast_path_metrics"]["summary_only"])
        self.assertEqual(entry["fast_path_metrics"]["semantic_granularity"], "summary_only")
        self.assertEqual(entry["fast_path_metrics"]["type_plan"], "VmSummaryOnly")
        self.assertEqual(entry["fast_path_metrics"]["decompile_plan"], "NativeSummaryIslands")
        self.assertEqual(entry["fast_path_metrics"]["interproc_iterations"], 1)
        self.assertTrue(entry["fast_path_metrics"]["interproc_has_summary"])
        self.assertEqual(entry["fast_path_metrics"]["phase_timings_us"]["semantic_summary"], 20)

    def test_adaptive_batch_timeout_preserves_successful_sections_and_marks_not_reached(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            first_batch_stdout = batched_stdout(
                [
                    ("t0_decompile_sla", 0, "int a(void) {\n  return 1;\n}"),
                    ("t0_decompile_pdd", 0, "int a(void) {\n  return 1;\n}"),
                    (
                        "t0_types",
                        0,
                        '{"ret_type":"int","params":[],"mutation_plan":{"mutations":[]}}',
                    ),
                    ("t0_profile", 0, '{"count":1}'),
                ]
            )
            responses = iter(
                [
                    cmd_result(first_batch_stdout, returncode=124),
                ]
            )
            seen_timeouts = []

            def runner(r2, path, cmd, timeout, env):
                seen_timeouts.append(timeout)
                return next(responses)

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=(),
                max_functions=4,
            )
            targets = [
                {"name": "sym.a", "addr": 0x1000, "found": True},
                {"name": "sym.b", "addr": 0x2000, "found": True},
            ]
            outputs, _events = benchmark.collect_targets_batched_adaptive(
                "r2",
                case,
                targets,
                30,
                1,
                False,
                {},
                Path(tmp),
                1,
                runner,
            )

        self.assertEqual(seen_timeouts, [30])
        self.assertEqual(outputs[0]["commands"]["decompile_sla"]["returncode"], 0)
        self.assertFalse(outputs[0]["commands"]["decompile_sla"]["timeout"])
        self.assertEqual(outputs[0]["attribution_mode"], "batch")
        self.assertEqual(outputs[1]["attribution_mode"], "batch")
        self.assertEqual(
            outputs[1]["commands"]["decompile_sla"]["section_status"],
            benchmark.BATCH_SECTION_NOT_REACHED,
        )
        self.assertTrue(outputs[1]["commands"]["decompile_sla"]["skipped"])
        self.assertTrue(benchmark.case_result_has_incomplete_work(
            {"targets": outputs},
            tuple(benchmark.TARGET_COMMAND_DEFS),
        ))
        self.assertEqual(
            benchmark.collect_failures({"discovery": {"returncode": 0}, "targets": outputs}),
            [],
        )

    def test_adaptive_batch_retry_only_retries_started_timeout_commands(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            partial_started = "\n".join(
                [
                    benchmark.batched_section_start("t0_decompile_sla", 0),
                    "partial",
                ]
            )
            responses = iter(
                [
                    cmd_result(partial_started, returncode=124),
                    cmd_result("", returncode=124),
                ]
            )

            def runner(r2, path, cmd, timeout, env):
                return next(responses)

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=(),
                max_functions=4,
            )
            outputs, _events = benchmark.collect_targets_batched_adaptive(
                "r2",
                case,
                [{"name": "sym.hot", "addr": 0x1000, "found": True}],
                30,
                1,
                False,
                {},
                Path(tmp),
                1,
                runner,
            )

        self.assertEqual(outputs[0]["attribution_mode"], "batch_with_command_retry")
        self.assertEqual(outputs[0]["retry_origin"], "batch_timeout")
        self.assertEqual(outputs[0]["retry_commands"], ["decompile_sla"])
        self.assertEqual(
            outputs[0]["commands"]["decompile_sla"]["attribution_mode"],
            "command_retry",
        )
        self.assertEqual(
            outputs[0]["commands"]["decompile_sla"]["retry_origin"],
            "batch_timeout",
        )
        self.assertEqual(
            benchmark.collect_failures({"discovery": {"returncode": 0}, "targets": outputs}),
            [{"kind": "timeout", "target": "sym.hot", "command": "decompile_sla"}],
        )

    def test_aggregate_is_sorted_and_scores_cases(self):
        cases = [
            {
                "name": "b",
                "corpus": "unit",
                "score": 90,
                "failures": [{"kind": "z", "target": "sym.hash_insert_if_absent"}],
                "targets": [],
            },
            {
                "name": "a",
                "corpus": "unit",
                "score": 100,
                "failures": [{"kind": "a", "target": "dbg.__xargmatch_internal"}],
                "case_events": [
                    {
                        "command": "case_setup",
                        "elapsed_s": 3.0,
                    }
                ],
                "targets": [
                    {
                        "name": None,
                        "requested": None,
                        "setup_event": {"elapsed_s": 0.5},
                        "commands": {
                            "types": {
                                "elapsed_s": 2.0,
                                "runtime_bucket": "fast",
                            },
                            "decompile_sla": {
                                "elapsed_s": 1.0,
                                "runtime_bucket": "fast",
                                "decompile_quality": {
                                    "classification": "fallback",
                                    "fallback_marker": "r2dec fallback:",
                                    "artifact_count": 2,
                                },
                            },
                            "decompile_pdg": {
                                "elapsed_s": 1.5,
                                "runtime_bucket": "normal",
                                "decompile_quality": {
                                    "classification": "structured",
                                    "artifact_count": 4,
                                },
                            },
                            "profile": {
                                "elapsed_s": 0.25,
                                "runtime_bucket": "fast",
                                "profile_metrics": {
                                    "engine_cache": {
                                        "analysis": {"hits": 1, "misses": 2},
                                        "artifacts": {"hits": 3, "misses": 4},
                                        "total": {"hits": 4, "misses": 6},
                                    }
                                },
                            },
                        },
                    }
                ],
            },
        ]
        summary = benchmark.aggregate(cases)

        self.assertEqual(summary["average_score"], 95.0)
        self.assertEqual(list(summary["failures_by_kind"].keys()), ["a", "z"])
        self.assertEqual(summary["slowest_commands"][0]["target"], None)
        self.assertEqual(summary["timing"]["case_setup_s"], 3.0)
        self.assertEqual(summary["timing"]["target_setup_s"], 0.5)
        self.assertEqual(summary["timing"]["command_s"], 4.75)
        self.assertEqual(summary["cache"]["engine"]["total"]["hits"], 4)
        self.assertEqual(summary["cache"]["engine"]["artifacts"]["misses"], 4)
        self.assertEqual(
            summary["quality"]["decompile_by_family"],
            {"unknown": {"fallback": 1, "structured": 1}},
        )
        self.assertEqual(summary["quality"]["fallback_by_family"], {"unknown": 1})
        self.assertEqual(summary["quality"]["pdg_comparison"]["common_targets"], 1)
        self.assertEqual(
            summary["quality"]["pdg_comparison"]["successful_common_targets"], 1
        )
        self.assertEqual(
            summary["quality"]["pdg_comparison"]["quality"],
            {"pdg": 1, "sla": 0, "tie": 0},
        )
        self.assertEqual(
            summary["quality"]["pdg_comparison"]["perf"],
            {"pdg": 0, "sla": 1, "tie": 0},
        )
        self.assertEqual(
            summary["quality"]["pdg_comparison"]["quality_then_perf"],
            {"pdg": 1, "sla": 0, "tie": 0},
        )
        self.assertEqual(
            summary["quality"]["pdg_comparison"]["by_corpus"]["unit"]["quality"],
            {"pdg": 1, "sla": 0, "tie": 0},
        )
        self.assertEqual(
            summary["quality"]["pdg_comparison"]["by_family"]["unknown"]["perf"],
            {"pdg": 0, "sla": 1, "tie": 0},
        )
        self.assertEqual(
            summary["quality"]["hard_failure_by_family"],
            {"argmatch": 1, "hash_table": 1},
        )
        self.assertEqual(summary["worst_targets"][0]["target"], None)
        self.assertEqual(summary["worst_targets"][0]["elapsed_s"], 4.75)

    def test_aggregate_summarizes_cache_and_summary_fast_paths(self):
        summary = benchmark.aggregate(
            [
                {
                    "name": "sample",
                    "corpus": "unit",
                    "score": 100,
                    "failures": [],
                    "targets": [
                        {
                            "name": "sym.worker",
                            "commands": {
                                "types": {
                                    "elapsed_s": 0.1,
                                    "runtime_bucket": "fast",
                                    "cache_metrics": {
                                        "summary_cache": {"hits": 4, "misses": 1, "lookups": 5},
                                    },
                                    "fast_path_metrics": {
                                        "cache_hit": True,
                                        "summary_fast_path": True,
                                        "summary_only": True,
                                        "semantic_granularity": "summary_only",
                                        "summary_attempted": 1,
                                        "native_worker_summary_count": 2,
                                        "phase_timings_us": {
                                            "interproc_summary": 10,
                                            "semantic_summary": 20,
                                        },
                                    },
                                }
                            },
                        }
                    ],
                }
            ]
        )

        self.assertEqual(summary["cache"]["summary"]["hits"], 4)
        self.assertNotIn("decompile", summary["cache"])
        self.assertEqual(summary["fast_paths"]["summary_fast_path_count"], 1)
        self.assertEqual(summary["fast_paths"]["summary_only_count"], 1)
        self.assertEqual(summary["fast_paths"]["cache_hit_commands"], 1)
        self.assertEqual(summary["fast_paths"]["semantic_granularity"], {"summary_only": 1})
        self.assertEqual(summary["fast_paths"]["phase_timings_us"]["semantic_summary"], 20)
        self.assertEqual(summary["fast_paths"]["counters"]["summary_attempted"], 1)
        self.assertEqual(summary["fast_paths"]["counters"]["native_worker_summary_count"], 2)

    def test_aggregate_reports_worst_targets_by_actionable_signal(self):
        summary = benchmark.aggregate(
            [
                {
                    "name": "coreutils-mf12",
                    "corpus": "coreutils",
                    "score": 80,
                    "failures": [
                        {"kind": "timeout", "target": "sym.hash_worker"},
                    ],
                    "targets": [
                        {
                            "name": "sym.residual_loop",
                            "commands": {
                                "decompile_sla": {
                                    "elapsed_s": 0.2,
                                    "decompile_quality": {"classification": "residual"},
                                },
                                "types": {
                                    "elapsed_s": 0.1,
                                    "type_metrics": {
                                        "generic_arg_count": 6,
                                        "generic_type_count": 1,
                                    },
                                },
                            },
                        },
                        {
                            "name": "dbg.string_scan",
                            "commands": {
                                "decompile_sla": {
                                    "elapsed_s": 0.3,
                                    "decompile_quality": {"classification": "structured"},
                                },
                                "types": {
                                    "elapsed_s": 0.2,
                                    "type_metrics": {
                                        "generic_arg_count": 2,
                                        "generic_type_count": 3,
                                    },
                                },
                            },
                        },
                        {
                            "name": "sym.hash_worker",
                            "commands": {
                                "decompile_sla": {
                                    "elapsed_s": 2.0,
                                    "decompile_quality": {"classification": "fallback"},
                                }
                            },
                        },
                    ],
                }
            ]
        )

        self.assertEqual(
            [target["target"] for target in summary["worst_targets"]],
            ["sym.hash_worker", "sym.residual_loop", "dbg.string_scan"],
        )
        self.assertEqual(summary["worst_targets"][0]["hard_failures"], 1)
        self.assertEqual(summary["worst_targets"][0]["failure_kinds"], ["timeout"])
        self.assertEqual(summary["worst_targets"][1]["residual_commands"], 1)
        self.assertEqual(summary["worst_targets"][1]["generic_arg_count"], 6)
        self.assertEqual(summary["worst_targets"][2]["generic_type_count"], 3)
        self.assertEqual(summary["worst_targets"][0]["elapsed_s"], 2.0)
        self.assertEqual(
            summary["quality"]["owner_buckets"],
            {"r2engine": 1, "r2sym": 1, "r2types": 12},
        )
        self.assertEqual(summary["worst_targets"][0]["owner_buckets"], {"r2engine": 1})
        self.assertEqual(
            summary["worst_targets"][1]["owner_buckets"],
            {"r2sym": 1, "r2types": 7},
        )
        self.assertEqual(summary["next_work"]["status"], "owner_work")
        self.assertEqual(
            summary["next_work"]["blocking_owners"],
            ["r2types", "r2engine", "r2sym"],
        )
        self.assertEqual(
            summary["next_work"]["owner_work_items"][0]["action"],
            benchmark.OWNER_ACTIONS["r2types"],
        )
        self.assertEqual(
            [target["target"] for target in summary["next_work"]["owner_work_items"][0]["targets"]],
            ["sym.residual_loop", "dbg.string_scan"],
        )
        self.assertEqual(summary["next_work"]["setup"]["status"], "ok")

    def test_aggregate_summarizes_manual_quality_gates(self):
        quality = benchmark.decompile_quality(
            "int f(void) {\n"
            "  while (1) { break; }\n"
            "  fcn.401000(arg1);\n"
            "  tmp:_2 = stack_8;\n"
            "}\n"
        )
        summary = benchmark.aggregate(
            [
                {
                    "name": "sample",
                    "corpus": "unit",
                    "score": 50,
                    "failures": [
                        {"kind": "argn_leak", "target": "sym.f"},
                        {"kind": "fake_stack_slot", "target": "sym.f"},
                        {"kind": "missing_return_nonvoid", "target": "sym.f"},
                        {"kind": "unresolved_fcn_or_temp_stack_leak", "target": "sym.f"},
                    ],
                    "targets": [
                        {
                            "name": "sym.f",
                            "commands": {
                                "decompile_sla": {
                                    "elapsed_s": 0.1,
                                    "runtime_bucket": "fast",
                                    "decompile_quality": quality,
                                }
                            },
                        }
                    ],
                }
            ]
        )

        self.assertEqual(
            summary["quality"]["manual_gate_failures"],
            {
                "argn_leak": 1,
                "fake_stack_slot": 1,
                "missing_return_nonvoid": 1,
                "unresolved_fcn_or_temp_stack_leak": 1,
            },
        )
        self.assertEqual(summary["quality"]["argn_leak_total"], 1)
        self.assertEqual(summary["quality"]["fake_call_arg_total"], 1)
        self.assertEqual(summary["quality"]["fake_stack_slot_total"], 1)
        self.assertEqual(summary["quality"]["fake_while_break_wrapper_total"], 1)
        self.assertEqual(summary["quality"]["missing_return_nonvoid_total"], 1)
        self.assertEqual(summary["quality"]["unresolved_fcn_total"], 1)
        self.assertGreaterEqual(summary["quality"]["raw_temp_stack_leak_total"], 2)

    def test_pdg_comparison_scores_readability_noise(self):
        summary = benchmark.aggregate(
            [
                {
                    "name": "cut",
                    "corpus": "coreutils",
                    "score": 100,
                    "failures": [],
                    "targets": [
                        {
                            "name": "dbg.skip_whitespace_run",
                            "commands": {
                                "decompile_sla": {
                                    "returncode": 0,
                                    "elapsed_s": 0.1,
                                    "decompile_quality": benchmark.decompile_quality(
                                        "int f(char *s) {\n  return *s;\n}\n"
                                    ),
                                },
                                "decompile_pdg": {
                                    "returncode": 0,
                                    "elapsed_s": 0.2,
                                    "decompile_quality": benchmark.decompile_quality(
                                        "int f(char *s) {\n"
                                        "  goto done;\n"
                                        "  return call_401000((void *)s) + (int)*s;\n"
                                        "done:\n"
                                        "  return 0;\n"
                                        "}\n"
                                    ),
                                },
                            },
                        }
                    ],
                }
            ]
        )

        comparison = summary["quality"]["pdg_comparison"]
        self.assertEqual(comparison["quality"], {"pdg": 0, "sla": 1, "tie": 0})
        self.assertEqual(comparison["perf"], {"pdg": 0, "sla": 1, "tie": 0})
        self.assertEqual(
            comparison["quality_then_perf"],
            {"pdg": 0, "sla": 1, "tie": 0},
        )
        self.assertEqual(comparison["by_corpus"]["coreutils"]["quality"]["sla"], 1)
        self.assertEqual(comparison["by_family"]["skip_whitespace_run"]["quality"]["sla"], 1)
        self.assertGreater(comparison["worst_quality_gaps"][0]["pdg_readability_smells"], 0)

    def test_pdg_comparison_reports_baseline_failures_without_scoring_them(self):
        summary = benchmark.aggregate(
            [
                {
                    "name": "cp",
                    "corpus": "coreutils",
                    "score": 100,
                    "failures": [],
                    "targets": [
                        {
                            "name": "dbg.main",
                            "commands": {
                                "decompile_sla": {
                                    "returncode": 0,
                                    "section_status": "completed",
                                    "elapsed_s": 0.01,
                                    "decompile_quality": {"classification": "structured"},
                                },
                                "decompile_pdg": {
                                    "returncode": -11,
                                    "section_status": "started_failed",
                                    "elapsed_s": 0.2,
                                    "decompile_quality": {"classification": "empty"},
                                },
                            },
                        }
                    ],
                }
            ]
        )

        comparison = summary["quality"]["pdg_comparison"]
        self.assertEqual(comparison["common_targets"], 1)
        self.assertEqual(comparison["successful_common_targets"], 0)
        self.assertEqual(comparison["pdg_failed"], 1)
        self.assertEqual(comparison["quality"], {"pdg": 0, "sla": 0, "tie": 0})
        self.assertEqual(comparison["perf"], {"pdg": 0, "sla": 0, "tie": 0})
        self.assertEqual(comparison["quality_then_perf"], {"pdg": 0, "sla": 0, "tie": 0})
        self.assertEqual(comparison["failed_targets"][0]["pdg_returncode"], -11)

    def test_batch_started_failure_is_retryable(self):
        target = {
            "found": True,
            "batch_event": {"returncode": -11},
            "commands": {
                "decompile_sla": {
                    "returncode": 0,
                    "section_status": "completed",
                },
                "decompile_pdg": {
                    "returncode": -11,
                    "section_status": "started_failed",
                },
                "types": {
                    "returncode": None,
                    "section_status": "not_reached",
                },
            },
        }

        self.assertTrue(benchmark.target_has_retryable_command(target))
        self.assertEqual(
            benchmark.retryable_command_names(target),
            {"decompile_pdg", "types"},
        )
        self.assertEqual(benchmark.timed_out_command_names(target), set())

    def test_worst_targets_reports_actionable_offenders(self):
        cases = [
            {
                "name": "test",
                "corpus": "coreutils",
                "targets": [
                    {
                        "name": "sym.binop",
                        "attribution_mode": "command",
                        "commands": {
                            "decompile_sla": {
                                "elapsed_s": 120.0,
                                "timeout": True,
                                "attribution_mode": "command",
                                "retry_origin": "target_timeout",
                                "decompile_quality": {"classification": "empty"},
                            },
                            "types": {
                                "elapsed_s": 0.2,
                                "type_metrics": {
                                    "generic_arg_count": 1,
                                    "generic_type_count": 2,
                                    "ret_type": "void*",
                                },
                            },
                        },
                    },
                    {
                        "name": "sym.quotearg_n_options",
                        "commands": {
                            "decompile_pdd": {
                                "elapsed_s": 0.1,
                                "decompile_quality": {"classification": "fallback"},
                            }
                        },
                    },
                ],
            }
        ]

        worst = benchmark.worst_targets(cases)

        self.assertEqual(worst["timeouts"][0]["target"], "sym.binop")
        self.assertEqual(worst["timeouts"][0]["retry_origin"], "target_timeout")
        self.assertEqual(worst["fallbacks"][0]["family"], "quote_options")
        self.assertEqual(worst["generic_type_targets"][0]["generic_count"], 3)
        self.assertEqual(worst["retry_attribution"]["command"], 1)
        self.assertEqual(worst["retry_attribution"]["command:command"], 1)

    def test_resume_reuses_only_matching_configured_cases(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "sample"
            binary.write_bytes(b"\x00")
            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=("sym.hot",),
                max_functions=1,
            )
            plugin_info = {"hash": "plugin-a", "files": []}
            args = type(
                "Args",
                (),
                {
                    "isolate_commands": False,
                    "batch_target_size": 2,
                    "r2": "r2",
                    "analysis": "aaa",
                    "repeat": 1,
                    "timeout": 30,
                    "include_sensitive": False,
                    "manifest": "",
                    "manifest_only": False,
                    "focused_coreutils": False,
                    "no_repo_fixtures": True,
                    "max_binaries_per_corpus": 0,
                    "target": ["sym.hot"],
                    "commands": "",
                    "baseline_plugin_dir": [],
                },
            )()
            config = benchmark.benchmark_execution_config(
                args,
                plugin_info,
                total_jobs=1,
                case_jobs=1,
                command_jobs=1,
            )
            key = benchmark.case_cache_key(case, config["run_config_hash"])
            report = {
                "schema": benchmark.SCHEMA_VERSION,
                "benchmark_config": config,
                "cases": [
                    {
                        "name": "sample",
                        "benchmark_case_key": key,
                        "score": 100,
                        "failures": [],
                    }
                ],
            }
            out = root / "report.json"
            out.write_text(json.dumps(report))

            loaded = benchmark.load_resume_cases(out, config["run_config_hash"])
            skipped = benchmark.load_resume_cases(out, "different")

        self.assertEqual(loaded[key]["score"], 100)
        self.assertEqual(skipped, {})

    def test_run_cases_with_checkpoint_writes_resumed_and_completed_cases(self):
        cases = [
            benchmark.BinaryCase("a", Path("/tmp/a"), "unit", "aaa", (), 1),
            benchmark.BinaryCase("b", Path("/tmp/b"), "unit", "aaa", (), 1),
        ]
        keys = ["ka", "kb"]
        checkpoints = []

        def checkpoint(results, resumed):
            checkpoints.append(([result["name"] for result in results], resumed))

        def worker(case, cached):
            self.assertIsNone(cached)
            return {"name": case.name, "failures": [], "score": 100, "targets": []}

        results, resumed = benchmark.run_cases_with_checkpoint(
            cases,
            1,
            worker,
            case_keys=keys,
            resume_cases={"ka": {"name": "a", "failures": [], "score": 90, "targets": []}},
            command_names=tuple(benchmark.TARGET_COMMAND_DEFS),
            checkpoint=checkpoint,
        )

        self.assertEqual(resumed, 1)
        self.assertEqual([result["name"] for result in results], ["a", "b"])
        self.assertTrue(results[0]["resumed_from_checkpoint"])
        self.assertEqual(results[1]["benchmark_case_key"], "kb")
        self.assertEqual(checkpoints[-1], (["a", "b"], 1))

    def test_target_command_checkpoint_runs_only_missing_commands(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            commands = benchmark.target_commands(("decompile_sla", "types"))
            cached_case = {
                "targets": [
                    {
                        "name": "sym.hot",
                        "addr": 0x1000,
                        "found": True,
                        "commands": {
                            "decompile_sla": {
                                "returncode": 0,
                                "timeout": False,
                                "elapsed_s": 0.1,
                                "runtime_bucket": "fast",
                                "stdout": benchmark.summarize_text("", include_preview=False),
                                "decompile_quality": {"classification": "structured"},
                            }
                        },
                    }
                ]
            }
            targets = benchmark.attach_cached_target_commands(
                [{"name": "sym.hot", "addr": 0x1000, "found": True}],
                cached_case,
                commands,
            )
            batch_stdout = batched_stdout(
                [
                    (
                        "t0_types",
                        0,
                        '{"ret_type":"int","params":[],"mutation_plan":{"mutations":[]}}',
                    )
                ]
            )
            seen_commands = []

            def runner(r2, path, cmd, timeout, env):
                seen_commands.append(cmd)
                return cmd_result(batch_stdout)

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=(),
                max_functions=4,
            )
            outputs, _events = benchmark.collect_targets_batched_case(
                "r2",
                case,
                targets,
                30,
                1,
                False,
                {},
                Path(tmp),
                runner,
                commands,
            )

        self.assertIn("a:sla.debug.types", seen_commands[0])
        self.assertNotIn("a:sla.dec", seen_commands[0])
        self.assertTrue(outputs[0]["commands"]["decompile_sla"]["resumed_from_checkpoint"])
        self.assertEqual(outputs[0]["commands"]["types"]["returncode"], 0)
        self.assertFalse(
            benchmark.case_result_has_incomplete_work(
                {"targets": outputs},
                ("decompile_sla", "types"),
            )
        )

    def test_collect_command_events_and_compare_reports(self):
        cases = [
            {
                "targets": [
                    {
                        "command_events": [
                            {
                                "case": "sample",
                                "corpus": "unit",
                                "target": "sym.f",
                                "command": "types",
                                "repeat_idx": 0,
                                "started_at": 2.0,
                                "ended_at": 3.0,
                                "elapsed_s": 1.0,
                                "timeout": False,
                                "returncode": 0,
                            },
                            {
                                "case": "sample",
                                "corpus": "unit",
                                "target": "sym.f",
                                "command": "decompile_sla",
                                "repeat_idx": 0,
                                "started_at": 1.0,
                                "ended_at": 1.5,
                                "elapsed_s": 0.5,
                                "timeout": False,
                                "returncode": 0,
                            },
                        ]
                    }
                ]
            }
        ]
        self.assertEqual(
            [event["command"] for event in benchmark.collect_command_events(cases)],
            ["decompile_sla", "types"],
        )

        before = {
            "status": "issues",
            "elapsed_s": 20.0,
            "summary": {
                "average_score": 70.0,
                "min_score": 10,
                "failures_by_kind": {"command_return": 1, "json_parse": 1},
                "quality": {
                    "decompile": {"residual": 5},
                    "generic_arg_total": 9,
                    "generic_type_total": 12,
                    "radare2_candidate_count": 2,
                },
                "next_work": {"status": "owner_work", "blocking_owners": ["r2types"]},
                "slowest_commands": [
                    {
                        "corpus": "unit",
                        "case": "sample",
                        "target": "sym.f",
                        "command": "types",
                        "elapsed_s": 10.0,
                    }
                ],
            },
        }
        after = {
            "status": "ok",
            "elapsed_s": 8.0,
            "summary": {
                "average_score": 95.0,
                "min_score": 90,
                "failures_by_kind": {},
                "quality": {
                    "decompile": {"residual": 2},
                    "generic_arg_total": 4,
                    "generic_type_total": 5,
                    "radare2_candidate_count": 0,
                },
                "next_work": {"status": "clean", "blocking_owners": []},
                "slowest_commands": [
                    {
                        "corpus": "unit",
                        "case": "sample",
                        "target": "sym.f",
                        "command": "types",
                        "elapsed_s": 3.0,
                    }
                ],
            },
        }

        delta = benchmark.compare_reports(before, after)
        self.assertEqual(delta["metrics"]["hard_failures"]["delta"], -2.0)
        self.assertEqual(delta["metrics"]["average_score"]["delta"], 25.0)
        self.assertEqual(
            delta["metrics"]["next_work_status"],
            {"before": "owner_work", "after": "clean"},
        )
        self.assertEqual(delta["next_work"]["after"]["status"], "clean")
        self.assertEqual(delta["slowest_command_delta"][0]["delta_s"], -7.0)

    def test_strict_quality_gate_checks_broad_quality_thresholds(self):
        args = type(
            "Args",
            (),
            {
                "max_hard_failures": 0,
                "max_residual_decompile": 2,
                "max_generic_args": 4,
                "max_generic_types": 5,
                "min_average_score": 99.0,
                "max_setup_command_ratio": 1.5,
                "require_pdg_comparison": True,
                "max_pdg_quality_wins": 0,
                "max_pdg_perf_wins": 0,
                "max_pdg_quality_then_perf_wins": 0,
            },
        )()
        report = {
            "summary": {
                "average_score": 98.5,
                "failures_by_kind": {"command_return": 1},
                "timing": {"setup_to_command_ratio": 2.0},
                "quality": {
                    "decompile": {"residual": 3},
                    "generic_arg_total": 4,
                    "generic_type_total": 8,
                    "pdg_comparison": {
                        "successful_common_targets": 0,
                        "quality": {"pdg": 1},
                        "perf": {"pdg": 2},
                        "quality_then_perf": {"pdg": 3},
                    },
                },
            }
        }

        gate = benchmark.strict_quality_gate(args, report)

        self.assertEqual(gate["status"], "failed")
        self.assertEqual(
            {failure["metric"] for failure in gate["failures"]},
            {
                "average_score",
                "generic_types",
                "hard_failures",
                "pdg_perf_wins",
                "pdg_quality_wins",
                "pdg_quality_then_perf_wins",
                "pdg_successful_common_targets",
                "residual_decompile",
                "setup_command_ratio",
            },
        )
        self.assertEqual(gate["checks"]["generic_args"]["value"], 4)

    def test_closure_gate_fails_incomplete_and_fake_semantics_even_with_high_score(self):
        args = type(
            "Args",
            (),
            {
                "closure_gate": True,
                "max_hard_failures": 0,
                "max_residual_decompile": 0,
                "max_generic_args": 0,
                "max_generic_types": 0,
                "min_average_score": 99.5,
                "max_setup_command_ratio": None,
                "require_pdg_comparison": False,
                "max_pdg_quality_wins": None,
                "max_pdg_perf_wins": None,
                "max_pdg_quality_then_perf_wins": None,
                "max_gold_failures": 0,
                "require_gold": False,
            },
        )()
        report = {
            "status": "incomplete",
            "summary": {
                "average_score": 100.0,
                "failures_by_kind": {},
                "quality": {
                    "decompile": {},
                    "empty_loop_body_total": 1,
                    "fake_stack_slot_total": 1,
                    "fake_while_break_wrapper_total": 0,
                    "missing_summary_role_certificate_total": 1,
                    "missing_summary_render_contract_total": 1,
                    "proof_coverage_gap_total": 1,
                    "summary_pseudo_call_total": 0,
                    "raw_temp_stack_leak_total": 1,
                    "undefined_identifier_return_total": 1,
                    "generic_arg_total": 0,
                    "generic_type_total": 0,
                    "gold_oracle": {"failures": 0, "expectations": 0},
                    "pdg_comparison": {},
                },
            },
        }

        gate = benchmark.strict_quality_gate(args, report)

        self.assertEqual(gate["status"], "failed")
        self.assertIn(
            "report_complete", {failure["metric"] for failure in gate["failures"]}
        )
        self.assertIn(
            "fake_semantics", {failure["metric"] for failure in gate["failures"]}
        )
        self.assertIn(
            "fake_stack_slots", {failure["metric"] for failure in gate["failures"]}
        )
        self.assertIn(
            "summary_role_certificate_gap",
            {failure["metric"] for failure in gate["failures"]},
        )
        self.assertIn(
            "summary_render_contract_gap",
            {failure["metric"] for failure in gate["failures"]},
        )
        self.assertIn(
            "proof_coverage_gap", {failure["metric"] for failure in gate["failures"]}
        )
        self.assertIn(
            "raw_temp_stack_leak", {failure["metric"] for failure in gate["failures"]}
        )
        self.assertIn(
            "undefined_identifier_return",
            {failure["metric"] for failure in gate["failures"]},
        )
        self.assertIn(
            "gold_expectations",
            {failure["metric"] for failure in gate["failures"]},
        )

    def test_parallel_split_uses_case_and_command_workers(self):
        self.assertEqual(benchmark.parallel_split(1, 12), (1, 1))
        self.assertEqual(benchmark.parallel_split(64, 1), (1, 64))
        self.assertEqual(benchmark.parallel_split(64, 6), (6, 10))

    def test_apply_preset_defaults_is_conservative(self):
        args = type(
            "Args",
            (),
            {
                "preset": "tier1",
                "focused_coreutils": False,
                "max_functions": benchmark.DEFAULT_MAX_FUNCTIONS,
                "timeout": benchmark.DEFAULT_TIMEOUT,
                "max_binaries_per_corpus": benchmark.DEFAULT_MAX_BINARIES_PER_CORPUS,
                "batch_target_size": 0,
                "commands": "",
            },
        )()

        benchmark.apply_preset_defaults(args)

        self.assertTrue(args.focused_coreutils)
        self.assertEqual(args.max_functions, 12)
        self.assertEqual(args.timeout, 120)
        self.assertEqual(args.batch_target_size, 0)
        self.assertEqual(args.commands, "decompile_sla,types,profile")

    def test_closure_gate_defaults_to_strict_gold_thresholds(self):
        args = type(
            "Args",
            (),
            {
                "preset": "",
                "focused_coreutils": False,
                "max_functions": benchmark.DEFAULT_MAX_FUNCTIONS,
                "timeout": benchmark.DEFAULT_TIMEOUT,
                "max_binaries_per_corpus": benchmark.DEFAULT_MAX_BINARIES_PER_CORPUS,
                "batch_target_size": 0,
                "commands": "decompile_sla,decompile_pdg,types,profile",
                "closure_gate": True,
                "strict": False,
                "max_hard_failures": None,
                "max_residual_decompile": None,
                "max_generic_args": None,
                "max_generic_types": None,
                "min_average_score": None,
                "max_setup_command_ratio": None,
                "require_pdg_comparison": False,
                "max_pdg_quality_wins": None,
                "max_pdg_perf_wins": None,
                "max_pdg_quality_then_perf_wins": None,
            },
        )()

        benchmark.apply_preset_defaults(args)

        self.assertTrue(args.strict)
        self.assertEqual(args.max_hard_failures, 0)
        self.assertEqual(args.max_residual_decompile, 0)
        self.assertEqual(args.max_generic_args, 0)
        self.assertEqual(args.max_generic_types, 0)
        self.assertEqual(args.min_average_score, 99.5)
        self.assertEqual(args.max_setup_command_ratio, 2.0)
        self.assertEqual(args.max_gold_failures, 0)
        self.assertTrue(args.require_gold)
        self.assertTrue(args.require_pdg_comparison)
        self.assertEqual(args.max_pdg_quality_wins, 0)
        self.assertIsNone(args.max_pdg_perf_wins)
        self.assertEqual(args.max_pdg_quality_then_perf_wins, 0)

    def test_cache_probe_defaults_to_repeated_tier1_commands(self):
        args = type(
            "Args",
            (),
            {
                "preset": "",
                "focused_coreutils": False,
                "max_functions": benchmark.DEFAULT_MAX_FUNCTIONS,
                "timeout": benchmark.DEFAULT_TIMEOUT,
                "max_binaries_per_corpus": benchmark.DEFAULT_MAX_BINARIES_PER_CORPUS,
                "batch_target_size": 0,
                "commands": "",
                "repeat": 1,
                "cache_probe": True,
                "isolate_commands": False,
                "r2": "r2",
                "analysis": "aaa",
                "include_sensitive": False,
                "manifest": "",
                "manifest_only": False,
                "no_repo_fixtures": False,
                "target": [],
                "baseline_plugin_dir": [],
            },
        )()

        benchmark.apply_preset_defaults(args)
        config = benchmark.benchmark_execution_config(
            args,
            {"hash": "plugin-a", "files": []},
            total_jobs=1,
            case_jobs=1,
            command_jobs=1,
        )

        self.assertEqual(args.repeat, 2)
        self.assertEqual(args.commands, "decompile_sla,types,profile")
        self.assertTrue(config["cache_probe"])
        self.assertEqual(config["repeat"], 2)

    def test_manifest_max_functions_can_be_overridden_for_broad_runs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "sample"
            binary.write_bytes(b"\x00")
            manifest = root / "manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "binaries": [
                            {
                                "name": "sample",
                                "path": str(binary),
                                "analysis": "aaa",
                                "max_functions": 6,
                            }
                        ]
                    }
                )
            )

            pinned = benchmark.read_manifest(manifest, "aaa", 100)
            broad = benchmark.read_manifest(manifest, "aaa", 100, True)

        self.assertEqual(pinned[0].max_functions, 6)
        self.assertEqual(broad[0].max_functions, 100)

    def test_pdg_is_explicit_decompiler_benchmark_command(self):
        self.assertIn("decompile_pdg", benchmark.TARGET_COMMAND_DEFS)
        self.assertEqual(benchmark.target_commands(("decompile_pdg",)), {"decompile_pdg": "pdg"})

    def test_build_r2_env_can_include_baseline_plugin_dir(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            plugin = root / "r2sleigh-plugin"
            baseline = root / "r2ghidra"
            plugin.mkdir()
            baseline.mkdir()
            plugin.joinpath("anal_sleigh.so").write_text("")
            baseline.joinpath("core_ghidra.so").write_text("")

            env = benchmark.build_r2_env("radare2", str(plugin), [str(baseline)], root / "tmp")

            merged = root / "tmp" / "plugins"
            self.assertEqual(env["R2_LIBR_PLUGINS"], str(merged))
            self.assertEqual(env["R2_USER_PLUGINS"], env["R2_LIBR_PLUGINS"])
            self.assertTrue(merged.joinpath("anal_sleigh.so").is_symlink())
            self.assertTrue(merged.joinpath("core_ghidra.so").is_symlink())

    def test_build_r2_env_canonicalizes_relative_plugin_dirs(self):
        env = benchmark.build_r2_env("radare2", "r2plugin", [], None)

        self.assertEqual(env["R2_LIBR_PLUGINS"], str((ROOT / "r2plugin").resolve()))

    def test_target_batches_split_large_batched_cases(self):
        targets = [{"name": f"f{i}"} for i in range(5)]

        batches = benchmark.target_batches(targets, 2)

        self.assertEqual([[item["name"] for item in batch] for batch in batches], [
            ["f0", "f1"],
            ["f2", "f3"],
            ["f4"],
        ])
        self.assertEqual(benchmark.target_batches(targets, 0), [targets])

    def test_case_batched_timeout_keeps_subprocess_cap(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "sample"
            binary.write_bytes(b"\x00")
            seen_timeouts = []

            def runner(r2, path, cmd, timeout, env):
                seen_timeouts.append(timeout)
                return cmd_result("")

            case = benchmark.BinaryCase(
                name="sample",
                path=binary,
                corpus="unit",
                analysis="aaa",
                targets=(),
                max_functions=4,
            )
            targets = [
                {"name": "sym.a", "addr": 0x1000, "found": True},
                {"name": "sym.b", "addr": 0x2000, "found": True},
                {"name": "sym.c", "addr": 0x3000, "found": True},
            ]
            outputs, events = benchmark.collect_targets_batched_case(
                "r2",
                case,
                targets,
                30,
                1,
                False,
                {},
                Path(tmp),
                runner,
            )

        self.assertEqual(seen_timeouts, [30])
        self.assertEqual(events[0]["timeout_s"], 30)
        self.assertEqual(outputs[0]["batch_event"]["timeout_s"], 30)

    def test_task_env_isolates_mutable_radare2_state(self):
        with tempfile.TemporaryDirectory() as tmp:
            env = benchmark.task_env({"KEEP": "1"}, Path(tmp), "case/name", "target 1")

            self.assertIsNotNone(env)
            assert env is not None
            self.assertEqual(env["KEEP"], "1")
            self.assertTrue(Path(env["HOME"]).is_dir())
            self.assertTrue(Path(env["XDG_DATA_HOME"]).is_dir())
            self.assertTrue(str(Path(env["HOME"])).startswith(str(Path(tmp))))

    def test_limited_runner_bounds_concurrent_subprocesses(self):
        active = 0
        max_active = 0
        lock = threading.Lock()

        def slow_runner(r2, path, cmd, timeout, env):
            nonlocal active, max_active
            with lock:
                active += 1
                max_active = max(max_active, active)
            time.sleep(0.02)
            with lock:
                active -= 1
            return cmd_result(cmd)

        limited = benchmark.LimitedRunner(slow_runner, 2)
        items = [str(idx) for idx in range(8)]
        outputs = benchmark.run_ordered_parallel(
            items,
            8,
            lambda item: limited("r2", Path("/tmp/bin"), item, 1, {}),
        )

        self.assertEqual([result.stdout for result in outputs], items)
        self.assertLessEqual(max_active, 2)


if __name__ == "__main__":
    unittest.main()
