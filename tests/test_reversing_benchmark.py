from __future__ import annotations

import hashlib
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


def cmd_result(
    stdout: str,
    returncode: int = 0,
    stderr: str = "",
    child_max_rss_bytes: int | None = None,
    stdout_bytes: bytes | None = None,
    stderr_bytes: bytes | None = None,
):
    return benchmark.CmdResult(
        returncode=returncode,
        stdout=stdout,
        stderr=stderr,
        elapsed_s=0.001,
        child_max_rss_bytes=child_max_rss_bytes,
        stdout_bytes=stdout_bytes,
        stderr_bytes=stderr_bytes,
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
            for check in benchmark.gold_checks_for_expectation(expectation):
                if check["check"] != "contains":
                    continue
                needle = check["pattern"]
                if any(marker in needle for marker in synthetic_markers):
                    offenders.append((expectation.get("id"), needle))

        self.assertEqual([], offenders)

    def test_checked_in_source_oracle_classifies_every_pattern(self):
        oracle_path = ROOT / "tests" / "gold" / "source_oracle.json"
        oracle = json.loads(oracle_path.read_text())
        self.assertEqual(oracle["schema"], 2)

        raw_check_count = 0
        for expectation in oracle["expectations"]:
            self.assertIn("checks", expectation)
            self.assertTrue(
                set(benchmark.GOLD_CHECK_KINDS).isdisjoint(expectation),
                expectation["id"],
            )
            checks = benchmark.gold_checks_for_expectation(
                expectation,
                context=expectation["id"],
                require_checks=True,
            )
            raw_check_count += len(checks)
            self.assertTrue(
                all(check["category"] != benchmark.GOLD_LEGACY_CATEGORY for check in checks),
                expectation["id"],
            )
            self.assertTrue(
                all(check["authority"] == "advisory" for check in checks),
                expectation["id"],
            )
            self.assertTrue(
                all(check["diagnostic"] in {"source_shape", "readability"} for check in checks),
                expectation["id"],
            )

        loaded = benchmark.load_gold_manifest(oracle_path)
        loaded_checks = [check for expectation in loaded for check in expectation["_gold_checks"]]
        self.assertEqual(len(loaded_checks), raw_check_count)
        self.assertEqual(
            {check["category"] for check in loaded_checks},
            {"semantic", "type", "structural", "cosmetic", "readability"},
        )

    def test_parse_json_payload_skips_non_json_prefix(self):
        output = "INFO: ignored {not json}\n[{\"ok\": true}]\nWARN: trailing text\n"
        self.assertEqual(benchmark.parse_json_payload(output), [{"ok": True}])

    def test_run_r2_preserves_timeout_partial_byte_output(self):
        stdout = mock.Mock()
        stdout.read.return_value = b"partial stdout \xff\n"
        stderr = mock.Mock()
        stderr.read.return_value = b"partial stderr \xfe\n"
        proc = mock.Mock(pid=123, stdout=stdout, stderr=stderr, returncode=None)
        usage = type("Usage", (), {"ru_maxrss": 7})()
        with (
            mock.patch.object(benchmark.subprocess, "Popen", return_value=proc) as popen,
            mock.patch.object(benchmark.os, "wait4", create=True),
            mock.patch.object(
                benchmark,
                "_wait4_with_timeout",
                return_value=(benchmark.signal.SIGKILL, usage, True),
            ),
        ):
            result = benchmark.run_r2(
                "r2",
                Path("/tmp/sample"),
                "aaa",
                1,
                {},
            )

        self.assertEqual(result.returncode, 124)
        self.assertEqual(result.stdout, "partial stdout �\n")
        self.assertEqual(result.stderr, "partial stderr �\n")
        self.assertEqual(result.stdout_bytes, b"partial stdout \xff\n")
        self.assertEqual(result.stderr_bytes, b"partial stderr \xfe\n")
        self.assertEqual(
            result.child_max_rss_bytes,
            benchmark.child_max_rss_bytes(usage.ru_maxrss),
        )
        self.assertEqual(
            popen.call_args.kwargs["start_new_session"],
            benchmark._process_groups_supported(),
        )

    def test_wait4_timeout_kills_child_group_and_reaps_direct_child(self):
        proc = mock.Mock(pid=321)
        usage = type("Usage", (), {"ru_maxrss": 9})()
        with (
            mock.patch.object(
                benchmark,
                "_wait4_nointr",
                side_effect=[(0, 0, None), (proc.pid, benchmark.signal.SIGKILL, usage)],
            ) as wait4,
            mock.patch.object(benchmark, "_process_groups_supported", return_value=True),
            mock.patch.object(benchmark.os, "killpg", create=True) as killpg,
        ):
            status, actual_usage, timed_out = benchmark._wait4_with_timeout(proc, 0)

        self.assertTrue(timed_out)
        self.assertEqual(status, benchmark.signal.SIGKILL)
        self.assertIs(actual_usage, usage)
        killpg.assert_called_once_with(proc.pid, benchmark.signal.SIGKILL)
        self.assertEqual(
            wait4.call_args_list,
            [mock.call(proc.pid, benchmark.os.WNOHANG), mock.call(proc.pid, 0)],
        )

    def test_child_max_rss_normalizes_linux_and_macos_units(self):
        self.assertEqual(benchmark.child_max_rss_bytes(7, "linux"), 7 * 1024)
        self.assertEqual(benchmark.child_max_rss_bytes(7, "darwin"), 7)
        self.assertIsNone(benchmark.child_max_rss_bytes(7, "win32"))
        self.assertIsNone(benchmark.child_max_rss_bytes(-1, "linux"))

    def test_phase0_manifest_matches_direct_child_rss_and_fresh_temp_contract(self):
        manifest = json.loads((ROOT / "doc" / "phase0-baseline-manifest.json").read_text())
        complete_output = next(
            metric for metric in manifest["required_metrics"] if metric["id"] == "complete_output"
        )
        peak_rss = next(
            metric for metric in manifest["required_metrics"] if metric["id"] == "peak_rss"
        )
        self.assertEqual(
            complete_output["current_support"],
            "available",
        )
        self.assertTrue(manifest["phase0_gate"]["baseline_reproducible"])
        self.assertTrue(manifest["phase0_gate"]["source_gold_raw_capture_verified"])
        self.assertTrue(manifest["phase0_gate"]["r2r_logs_verified"])
        self.assertTrue(manifest["phase0_gate"]["exact_command_provenance_verified"])
        self.assertIn("--raw-output-dir", complete_output["collector"])
        self.assertEqual(peak_rss["current_support"], "available")
        self.assertIn("direct radare2 child", peak_rss["scope"])
        self.assertIn("does not claim descendant", peak_rss["note"])
        for capture in manifest["commands"]:
            if capture["id"].endswith(("_cold", "_warm")):
                self.assertTrue(capture["command"].startswith('phase0_tmpdir="$(mktemp -d '))
                self.assertIn('--tmpdir "$phase0_tmpdir"', capture["command"])
                self.assertIn(
                    '--raw-output-dir "$phase0_tmpdir/raw-output"',
                    capture["command"],
                )

    def test_raw_output_archive_preserves_bytes_and_separates_adversarial_identities(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            archive = benchmark.RawOutputArchive(root / "raw")
            fixture_a = root / "fixtures" / "sample-a"
            fixture_b = root / "fixtures" / "sample-b"
            case_a = benchmark.BinaryCase(
                name="../../same case",
                path=fixture_a,
                corpus="unit/a",
                analysis="aaa",
                targets=(),
                max_functions=1,
            )
            case_b = benchmark.BinaryCase(
                name="../../same case",
                path=fixture_b,
                corpus="unit/b",
                analysis="aaa",
                targets=(),
                max_functions=1,
            )
            target_a = {"name": "../../sym?f", "addr": 0x1000}
            target_b = {"name": "..\\..//sym?f", "addr": 0x1000}
            raw_stdout = b"\x00\xffstdout\r\n\x80"
            raw_stderr = b"\xfeerror\x00\n"
            result = cmd_result(
                "\x00�stdout\r\n�",
                returncode=124,
                stderr="�error\x00\n",
                stdout_bytes=raw_stdout,
                stderr_bytes=raw_stderr,
            )

            identities = [
                (case_a, target_a, "isolated"),
                (case_a, target_b, "isolated"),
                (case_a, target_a, "command-retry/batch_timeout"),
                (case_b, target_a, "isolated"),
            ]
            records = [
                archive.record(
                    case=case,
                    target=target,
                    command="decompile/../../sla",
                    repeat_idx=0,
                    attempt=attempt,
                    result=result,
                    returncode=124,
                    timeout=True,
                    temperature="cold",
                )
                for case, target, attempt in identities
            ]

            metadata_paths = [record["metadata_path"] for record in records]
            self.assertEqual(len(set(metadata_paths)), len(records))
            for record in records:
                metadata_rel = Path(record["metadata_path"])
                self.assertFalse(metadata_rel.is_absolute())
                self.assertNotIn("..", metadata_rel.parts)
                metadata = json.loads((archive.root / metadata_rel).read_text())
                self.assertEqual(metadata["returncode"], 124)
                self.assertTrue(metadata["timeout"])
                for stream_name, expected in (
                    ("stdout", raw_stdout),
                    ("stderr", raw_stderr),
                ):
                    stream = metadata[stream_name]
                    self.assertEqual((archive.root / stream["path"]).read_bytes(), expected)
                    self.assertEqual(stream["length"], len(expected))
                    self.assertEqual(stream["sha256"], hashlib.sha256(expected).hexdigest())

            with self.assertRaises(FileExistsError):
                archive.record(
                    case=case_a,
                    target=target_a,
                    command="decompile/../../sla",
                    repeat_idx=0,
                    attempt="isolated",
                    result=result,
                    returncode=124,
                    timeout=True,
                    temperature="cold",
                )
            self.assertEqual(list(archive.root.rglob("*.tmp-*")), [])
            clone = benchmark.RawOutputArchive(root / "raw-clone")
            clone_record = clone.record(
                case=case_a,
                target=target_a,
                command="decompile/../../sla",
                repeat_idx=0,
                attempt="isolated",
                result=result,
                returncode=124,
                timeout=True,
                temperature="cold",
            )
            self.assertEqual(clone_record["metadata_path"], records[0]["metadata_path"])

            resumed = benchmark.RawOutputArchive(archive.root, load_existing=True)
            self.assertEqual(resumed.summary(False)["record_count"], len(records))
            self.assertEqual(resumed.summary(False)["root"], "<redacted:raw>")
            resumed_record = resumed.record(
                case=case_a,
                target=target_a,
                command="decompile/../../sla",
                repeat_idx=0,
                attempt="isolated",
                result=result,
                returncode=124,
                timeout=True,
                temperature="cold",
            )
            self.assertEqual(resumed_record["session_idx"], 1)
            self.assertNotEqual(resumed_record["metadata_path"], records[0]["metadata_path"])
            args = type(
                "Args",
                (),
                {
                    "r2": "r2",
                    "analysis": "aaa",
                    "repeat": 1,
                    "isolate_commands": True,
                    "batch_target_size": 0,
                    "manifest": "",
                    "gold_manifest": "",
                    "manifest_only": True,
                    "no_repo_fixtures": True,
                    "coreutils_dir": "",
                    "cgc_dir": "",
                    "juliet_dir": "",
                    "kernel": "",
                    "preset": "",
                    "resume": False,
                    "include_sensitive": False,
                },
            )()
            report = benchmark.build_benchmark_report(
                args,
                [],
                elapsed_s=0.0,
                total_jobs=1,
                case_jobs=1,
                command_jobs=1,
                total_cases=0,
                resumed_cases=0,
                plugin_info={"hash": "none", "files": []},
                benchmark_config={"run_config_hash": "test"},
                command_names=("decompile_sla",),
                raw_output_archive=resumed,
            )
            disabled_report = benchmark.build_benchmark_report(
                args,
                [],
                elapsed_s=0.0,
                total_jobs=1,
                case_jobs=1,
                command_jobs=1,
                total_cases=0,
                resumed_cases=0,
                plugin_info={"hash": "none", "files": []},
                benchmark_config={"run_config_hash": "test"},
                command_names=("decompile_sla",),
            )
            json.dumps(report)
            self.assertEqual(report["raw_output_archive"]["record_count"], len(records) + 1)
            self.assertEqual(
                disabled_report["raw_output_archive"],
                {"enabled": False, "record_count": 0, "records": []},
            )

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
                    "primary_failure_taxonomy": "structural",
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
            [
                {
                    "kind": "timeout",
                    "target": "sym.hot",
                    "command": "decompile_sla",
                    "primary_failure_taxonomy": "performance",
                }
            ],
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
        self.assertTrue(
            all(
                failure["primary_failure_taxonomy"]
                in {"semantic", "structural", "type", "readability", "performance"}
                for failure in failures
            )
        )
        self.assertLessEqual(benchmark.score_case(case_result), 34)

    def test_phase0_primary_failure_taxonomy_is_total_for_known_kinds(self):
        known = (
            set(benchmark.FAILURE_OWNER)
            | set(benchmark.QUALITY_GATE_FAILURES)
            | {
                "decompiler_fallback",
                "discovery_parse",
                "discovery_return",
                "empty_decompile",
                "json_parse",
                "missing_symbol_debug_target_alias",
                "summary_synthetic_local",
            }
        )
        self.assertEqual(
            [],
            sorted(known - set(benchmark.FAILURE_PRIMARY_TAXONOMY)),
        )
        self.assertEqual(
            {"semantic", "structural", "type", "readability", "performance"},
            set(benchmark.FAILURE_PRIMARY_TAXONOMY.values()),
        )
        self.assertEqual(
            "performance",
            benchmark.primary_failure_taxonomy(
                "nondeterministic_output", {"command": "profile"}
            ),
        )
        self.assertEqual(
            "semantic",
            benchmark.primary_failure_taxonomy(
                "nondeterministic_output", {"command": "decompile_sla"}
            ),
        )

    def test_profile_repeat_mismatch_is_measurement_observation_not_failure(self):
        case_result = {
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [
                {
                    "name": "sym.sample",
                    "commands": {
                        "profile": {"returncode": 0, "repeat": {"stable": False}},
                        "decompile_sla": {"returncode": 0, "repeat": {"stable": False}},
                    },
                }
            ],
        }

        failures = benchmark.collect_failures(case_result)

        self.assertEqual(
            ["nondeterministic_output"],
            [failure["kind"] for failure in failures],
        )
        self.assertEqual(
            [
                {
                    "kind": "unnormalized_profile_repeat_mismatch",
                    "target": "sym.sample",
                    "command": "profile",
                }
            ],
            case_result["measurement_observations"],
        )

    def test_gold_oracle_exact_c_mismatch_is_advisory_to_closure(self):
        case = benchmark.BinaryCase(
            name="sample",
            path=Path("/tmp/sample"),
            corpus="unit",
            analysis="aa",
            targets=("worker",),
            max_functions=1,
        )
        target = {"name": "sym.worker", "requested": "worker"}
        gold = [
            {
                "id": "exact-c-shape",
                "corpus": "unit",
                "case": "sample",
                "target": "worker",
                "command": "decompile_sla",
                "owner": "r2dec",
                "checks": {"semantic": {"contains": ["return 1;"]}},
            }
        ]
        entry = benchmark.command_summary(
            "decompile_sla",
            cmd_result("int worker(void) { return 0; }\n"),
            False,
            case=case,
            target=target,
            gold_manifest=gold,
        )
        case_result = {
            "name": "sample",
            "corpus": "unit",
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [{"name": target["name"], "commands": {"decompile_sla": entry}}],
        }
        failures = benchmark.collect_failures(case_result)
        case_result["failures"] = failures
        case_result["score"] = benchmark.score_case(case_result)
        summary = benchmark.aggregate([case_result])
        args = type(
            "Args",
            (),
            {
                "closure_gate": True,
                "max_hard_failures": 0,
                "max_residual_decompile": None,
                "max_generic_args": None,
                "max_generic_types": None,
                "min_average_score": None,
                "max_setup_command_ratio": None,
                "require_pdg_comparison": False,
                "max_pdg_quality_wins": None,
                "max_pdg_perf_wins": None,
                "max_pdg_quality_then_perf_wins": None,
                "max_gold_failures": 0,
                "require_gold": True,
            },
        )()
        gate = benchmark.strict_quality_gate(args, {"status": "ok", "summary": summary})

        advisory = entry["gold_oracle"]
        self.assertEqual(advisory["authority"], "advisory")
        self.assertEqual(advisory["status"], "advisory_mismatch")
        self.assertEqual(advisory["advisory_mismatch_count"], 1)
        self.assertEqual(
            advisory["advisory_mismatches"][0]["kind"],
            benchmark.GOLD_ORACLE_ADVISORY_MISMATCH,
        )
        self.assertEqual(advisory["advisory_mismatches"][0]["authority"], "advisory")
        self.assertEqual(failures, [])
        self.assertEqual(case_result["score"], 100)
        self.assertEqual(gate["status"], "ok")

        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            manifest_path = tmp_path / "gold.json"
            manifest_path.write_text(json.dumps({"expectations": gold}))
            argv = [
                "reversing_benchmark.py",
                "--closure-gate",
                "--require-gold",
                "--max-gold-failures",
                "0",
                "--gold-manifest",
                str(manifest_path),
                "--commands",
                "decompile_sla",
                "--out",
                str(tmp_path / "report.json"),
            ]
            with (
                mock.patch.object(sys, "argv", argv),
                mock.patch.object(benchmark, "build_cases", return_value=[case]),
                mock.patch.object(benchmark, "build_r2_env", return_value={}),
                mock.patch.object(benchmark, "plugin_fingerprint", return_value={}),
                mock.patch.object(
                    benchmark,
                    "run_cases_with_checkpoint",
                    return_value=([case_result], 0),
                ),
                mock.patch.object(benchmark, "write_report") as write_report,
                mock.patch("builtins.print"),
            ):
                exit_code = benchmark.main()

        main_report = write_report.call_args.args[1]
        self.assertEqual(exit_code, 0)
        self.assertEqual(main_report["status"], "ok")
        self.assertEqual(main_report["strict_quality_gate"]["status"], "ok")
        self.assertEqual(
            main_report["benchmark_config"]["source_shape_advisory"],
            {"authority": "advisory", "max_gold_failures_ignored": 0},
        )

    def test_execution_and_requested_gold_provenance_coverage_remain_hard(self):
        entry = benchmark.command_summary(
            "decompile_sla",
            cmd_result("", returncode=2, stderr="runner failed"),
            False,
        )
        case_result = {
            "name": "sample",
            "corpus": "unit",
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [{"name": "sym.worker", "commands": {"decompile_sla": entry}}],
        }
        case_result["failures"] = benchmark.collect_failures(case_result)
        case_result["score"] = benchmark.score_case(case_result)
        summary = benchmark.aggregate([case_result])
        args = type(
            "Args",
            (),
            {
                "closure_gate": False,
                "max_hard_failures": 0,
                "max_residual_decompile": None,
                "max_generic_args": None,
                "max_generic_types": None,
                "min_average_score": None,
                "max_setup_command_ratio": None,
                "require_pdg_comparison": False,
                "max_pdg_quality_wins": None,
                "max_pdg_perf_wins": None,
                "max_pdg_quality_then_perf_wins": None,
                "require_gold": True,
            },
        )()
        gate = benchmark.strict_quality_gate(args, {"status": "ok", "summary": summary})

        self.assertIn("command_return", {failure["kind"] for failure in case_result["failures"]})
        self.assertEqual(gate["status"], "failed")
        self.assertEqual(
            {failure["metric"] for failure in gate["failures"]},
            {"gold_expectations", "hard_failures"},
        )

        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = Path(tmp) / "gold.json"
            manifest_path.write_text(
                json.dumps(
                    {
                        "expectations": [
                            {
                                "target": "worker",
                                "command": "decompile_sla",
                                "owner": "not-a-canonical-owner",
                                "contains": ["return 1;"],
                            }
                        ]
                    }
                )
            )
            with self.assertRaisesRegex(ValueError, "owner must be one of"):
                benchmark.load_gold_manifest(manifest_path)

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
                "checks": {
                    "type": {"contains": ["DemoStruct*"]},
                    "readability": {
                        "contains": ["arr[idx].fourteenth + arr[idx].third"],
                        "not_contains": ["sla_struct_", "*(arr +"],
                    },
                },
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

        self.assertEqual(entry["gold_oracle"]["authority"], "advisory")
        self.assertEqual(entry["gold_oracle"]["status"], "matched")
        self.assertEqual(entry["gold_oracle"]["expectation_count"], 1)
        self.assertEqual(entry["gold_oracle"]["source_shape_check_count"], 1)
        self.assertEqual(entry["gold_oracle"]["readability_check_count"], 3)
        self.assertEqual(entry["gold_oracle"]["unclassified_check_count"], 0)
        self.assertEqual(entry["gold_oracle"]["advisory_mismatches"], [])

    def test_readability_gold_mismatch_stays_advisory(self):
        case = benchmark.BinaryCase(
            name="sample",
            path=Path("/tmp/sample"),
            corpus="unit",
            analysis="aaa",
            targets=("worker",),
            max_functions=1,
        )
        target = {"name": "sym.worker", "requested": "worker"}
        gold = [
            {
                "target": "worker",
                "command": "decompile_sla",
                "owner": "r2dec",
                "checks": {
                    "semantic": {"contains": ["return 1;"]},
                    "readability": {"contains": ["friendly_result_name"]},
                },
            }
        ]
        entry = benchmark.command_summary(
            "decompile_sla",
            cmd_result("int worker(void) { return 1; }\n"),
            False,
            case=case,
            target=target,
            gold_manifest=gold,
        )
        case_result = {
            "name": "sample",
            "corpus": "unit",
            "score": 100,
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [{"name": target["name"], "commands": {"decompile_sla": entry}}],
        }
        failures = benchmark.collect_failures(case_result)
        case_result["failures"] = failures
        summary = benchmark.aggregate([case_result])

        self.assertEqual(entry["gold_oracle"]["status"], "advisory_mismatch")
        self.assertEqual(
            [
                (mismatch["category"], mismatch["diagnostic"], mismatch["authority"])
                for mismatch in entry["gold_oracle"]["advisory_mismatches"]
            ],
            [("readability", "readability", "advisory")],
        )
        self.assertEqual(failures, [])
        self.assertEqual(summary["quality"]["gold_oracle"]["source_shape_mismatches"], 0)
        self.assertEqual(summary["quality"]["gold_oracle"]["readability_mismatches"], 1)

        args = type(
            "Args",
            (),
            {
                "closure_gate": False,
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
                "require_gold": False,
            },
        )()
        gate = benchmark.strict_quality_gate(args, {"summary": summary})
        self.assertNotIn("gold_failures", gate["checks"])

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
        self.assertEqual(
            expectations[0]["_gold_checks"],
            [
                {
                    "check": "contains",
                    "pattern": "return 1;",
                    "category": "unclassified",
                    "diagnostic": "unclassified",
                    "authority": "advisory",
                }
            ],
        )

    def test_load_gold_manifest_rejects_unknown_or_mixed_check_taxonomy(self):
        base = {
            "target": "dbg.worker",
            "command": "decompile_sla",
            "owner": "r2dec",
        }
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "gold.json"
            path.write_text(
                json.dumps(
                    {
                        "expectations": [
                            {**base, "checks": {"style": {"contains": ["worker"]}}}
                        ]
                    }
                )
            )
            with self.assertRaisesRegex(ValueError, "category 'style'"):
                benchmark.load_gold_manifest(path)

            path.write_text(
                json.dumps(
                    {
                        "expectations": [
                            {
                                **base,
                                "checks": {"semantic": {"contains": ["return 1;"]}},
                                "contains": ["worker"],
                            }
                        ]
                    }
                )
            )
            with self.assertRaisesRegex(ValueError, "cannot mix categorized checks"):
                benchmark.load_gold_manifest(path)

    def test_legacy_gold_mismatch_is_explicit_and_advisory(self):
        case = benchmark.BinaryCase(
            name="sample",
            path=Path("/tmp/sample"),
            corpus="unit",
            analysis="aaa",
            targets=("worker",),
            max_functions=1,
        )
        target = {"name": "sym.worker", "requested": "worker"}
        entry = benchmark.command_summary(
            "decompile_sla",
            cmd_result("int worker(void) { return 0; }\n"),
            False,
            case=case,
            target=target,
            gold_manifest=[
                {
                    "target": "worker",
                    "command": "decompile_sla",
                    "owner": "r2dec",
                    "contains": ["return 1;"],
                }
            ],
        )
        case_result = {
            "discovery": {"returncode": 0, "function_count": 1},
            "targets": [{"name": target["name"], "commands": {"decompile_sla": entry}}],
        }

        self.assertEqual(entry["gold_oracle"]["authority"], "advisory")
        self.assertEqual(entry["gold_oracle"]["status"], "advisory_mismatch")
        self.assertEqual(
            (
                entry["gold_oracle"]["advisory_mismatches"][0]["category"],
                entry["gold_oracle"]["advisory_mismatches"][0]["diagnostic"],
            ),
            ("unclassified", "unclassified"),
        )
        self.assertEqual(benchmark.collect_failures(case_result), [])

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
        self.assertEqual(quality["classification"], "residual")
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

    def test_in_process_timer_is_removed_from_payload_and_charges_only_command(self):
        stdout = "\n".join(
            [
                benchmark.batched_section_start("profile", 0),
                '{"count":1}',
                "0.000123",
                benchmark.batched_time_marker("ELAPSED", "profile", 0),
                benchmark.batched_section_end("profile", 0),
            ]
        )

        sections, timings = benchmark.parse_batched_output(stdout)
        byte_sections = benchmark.parse_batched_sections_bytes(stdout.encode())

        self.assertEqual(sections[("profile", 0)], '{"count":1}\n')
        self.assertEqual(byte_sections[("profile", 0)], b'{"count":1}\n')
        self.assertEqual(
            timings[("profile", 0)],
            (benchmark.IN_PROCESS_TIMER_START_NS, 123_000),
        )
        self.assertEqual(
            benchmark.timing_elapsed_s(*timings[("profile", 0)]),
            0.000123,
        )
        script = "; ".join(benchmark.batched_timed_command("profile", 0, "a:sla.debug.profilej"))
        self.assertIn("?t a:sla.debug.profilej", script)
        self.assertNotIn("!date", script)

    def test_isolated_command_event_excludes_process_and_setup_overhead(self):
        case = benchmark.BinaryCase(
            "sample",
            Path("/tmp/sample"),
            "unit",
            "aaa",
            (),
            1,
        )
        stdout = "\n".join(
            [
                benchmark.batched_section_start("profile", 0),
                '{"count":1}',
                "0.000123",
                benchmark.batched_time_marker("ELAPSED", "profile", 0),
                benchmark.batched_section_end("profile", 0),
            ]
        )
        seen_scripts = []

        def runner(r2, path, cmd, timeout, env):
            seen_scripts.append(cmd)
            return benchmark.CmdResult(0, stdout, "", 9.0, 123)

        target = benchmark.collect_target(
            "r2",
            case,
            {"name": "sym.f", "addr": 0x1000, "found": True},
            30,
            1,
            False,
            {},
            None,
            1,
            runner,
            {"profile": "a:sla.debug.profilej"},
        )

        event = target["command_events"][0]
        self.assertEqual(event["elapsed_s"], 0.000123)
        self.assertEqual(event["timer"], "r2_prof")
        self.assertEqual(target["commands"]["profile"]["elapsed_s"], 0.000123)
        self.assertEqual(target["commands"]["profile"]["stdout"]["bytes"], 12)
        self.assertNotIn("!date", seen_scripts[0])

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

    def test_parse_batched_sections_bytes_preserves_non_utf8_payload(self):
        payload = b"\x00\xffpayload\r\n\x80without-final-newline"
        stdout = (
            benchmark.batched_section_start("decompile_sla", 0).encode("ascii")
            + b"\n"
            + payload
            + b"\n"
            + benchmark.batched_section_end("decompile_sla", 0).encode("ascii")
            + b"\n"
        )

        sections = benchmark.parse_batched_sections_bytes(stdout)

        self.assertEqual(sections[("decompile_sla", 0)], payload + b"\n")

    def test_batched_temperatures_are_explicit_without_section_rss_attribution(self):
        case = benchmark.BinaryCase(
            name="sample",
            path=Path("/tmp/sample"),
            corpus="unit",
            analysis="aaa",
            targets=(),
            max_functions=1,
        )
        stdout = batched_stdout(
            [
                ("decompile_sla", 0, "int f(void) { return 1; }"),
                ("decompile_sla", 1, "int f(void) { return 1; }"),
            ]
        )

        def runner(r2, path, cmd, timeout, env):
            return cmd_result(stdout, child_max_rss_bytes=64 * 1024 * 1024)

        with tempfile.TemporaryDirectory() as tmp:
            archive = benchmark.RawOutputArchive(Path(tmp) / "raw")
            target = benchmark.collect_target_batched(
                "r2",
                case,
                {"name": "sym.f", "addr": 0x1000, "found": True},
                30,
                2,
                False,
                {},
                None,
                runner,
                {"decompile_sla": "a:sla.dec"},
                raw_output_archive=archive,
            )
            archive_summary = archive.summary(True)

        command_events = [
            event
            for event in target["command_events"]
            if event["command"] == "decompile_sla"
        ]
        self.assertEqual(
            [event["temperature"] for event in command_events],
            ["cold", "warm"],
        )
        self.assertEqual(target["batch_event"]["child_max_rss_bytes"], 64 * 1024 * 1024)
        self.assertTrue(
            all("child_max_rss_bytes" not in event for event in target["command_events"])
        )
        self.assertEqual(archive_summary["record_count"], 2)
        self.assertTrue(
            all(event.get("raw_output_metadata") for event in command_events)
        )
        self.assertTrue(
            all(record["stdout"]["scope"] == "batch_section" for record in archive_summary["records"])
        )

    def test_batched_warm_pass_repeats_full_tier1_sequence(self):
        case = benchmark.BinaryCase("sample", Path("/tmp/sample"), "unit", "aaa", (), 1)
        sections = benchmark.batched_target_script(
            case,
            0x1000,
            2,
            benchmark.target_commands(("decompile_sla", "types", "profile")),
        )

        self.assertEqual(
            [(name, repeat_idx) for name, repeat_idx, _marker, _command in sections],
            [
                ("decompile_sla", 0),
                ("types", 0),
                ("profile", 0),
                ("decompile_sla", 1),
                ("types", 1),
                ("profile", 1),
            ],
        )

    def test_isolated_repeats_are_cold_children_with_individual_rss(self):
        case = benchmark.BinaryCase(
            name="sample",
            path=Path("/tmp/sample"),
            corpus="unit",
            analysis="aaa",
            targets=(),
            max_functions=1,
        )
        responses = iter(
            [
                cmd_result("int f(void) { return 1; }", child_max_rss_bytes=10),
                cmd_result("int f(void) { return 1; }", child_max_rss_bytes=20),
            ]
        )

        def runner(r2, path, cmd, timeout, env):
            return next(responses)

        with tempfile.TemporaryDirectory() as tmp:
            archive = benchmark.RawOutputArchive(Path(tmp) / "raw")
            target = benchmark.collect_target(
                "r2",
                case,
                {"name": "sym.f", "addr": 0x1000, "found": True},
                30,
                2,
                False,
                {},
                None,
                1,
                runner,
                {"decompile_sla": "a:sla.dec"},
                raw_output_archive=archive,
            )
            archive_summary = archive.summary(True)

        events = target["command_events"]
        self.assertEqual([event["temperature"] for event in events], ["cold", "cold"])
        self.assertEqual([event["child_max_rss_bytes"] for event in events], [10, 20])
        self.assertEqual(archive_summary["record_count"], 2)
        self.assertTrue(all(event.get("raw_output_metadata") for event in events))

    def test_run_case_batched_scores_clean_outputs_and_reports_analysis_cache_hits(self):
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
                        '"total":{"hits":1,"misses":2,"lookups":3,"insertions":2,"evictions":0}}}'
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
            1,
        )
        self.assertNotIn(
            "artifacts",
            target["commands"]["profile"]["profile_metrics"]["engine_cache"],
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
            [
                {
                    "kind": "timeout",
                    "target": "sym.hot",
                    "command": "decompile_sla",
                    "primary_failure_taxonomy": "performance",
                }
            ],
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
                                        "total": {"hits": 1, "misses": 2},
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
        self.assertEqual(summary["cache"]["engine"]["total"]["hits"], 1)
        self.assertNotIn("artifacts", summary["cache"]["engine"])
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

    def test_aggregate_separates_temperature_and_reports_peak_child_rss(self):
        summary = benchmark.aggregate(
            [
                {
                    "name": "sample",
                    "corpus": "unit",
                    "score": 100,
                    "failures": [],
                    "discovery": {"child_max_rss_bytes": 80},
                    "targets": [
                        {
                            "name": "sym.f",
                            "batch_event": {"child_max_rss_bytes": 300},
                            "command_events": [
                                {
                                    "command": "decompile_sla",
                                    "temperature": "cold",
                                    "elapsed_s": 1.0,
                                    "child_max_rss_bytes": 100,
                                },
                                {
                                    "command": "decompile_sla",
                                    "temperature": "warm",
                                    "elapsed_s": 0.25,
                                },
                                {
                                    "command": "types",
                                    "temperature": "cold",
                                    "elapsed_s": 0.5,
                                    "child_max_rss_bytes": 200,
                                },
                                {
                                    "command": "setup",
                                    "temperature": "cold",
                                    "elapsed_s": 10.0,
                                },
                                {
                                    "command": "profile",
                                    "temperature": "cold",
                                    "elapsed_s": 9.0,
                                    "section_status": benchmark.BATCH_SECTION_NOT_REACHED,
                                },
                            ],
                            "commands": {},
                        }
                    ],
                }
            ]
        )

        self.assertEqual(
            summary["timing"]["by_temperature"],
            {
                "cold": {"count": 2, "elapsed_s": 1.5},
                "warm": {"count": 1, "elapsed_s": 0.25},
            },
        )
        self.assertEqual(summary["memory"], {"peak_child_rss_bytes": 300})
        self.assertEqual(benchmark.SCHEMA_VERSION, 11)

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
                        "batch_event": {
                            "case": "sample",
                            "command": "case_batch",
                            "started_at": 1.0,
                            "ended_at": 2.0,
                            "returncode": 0,
                            "child_max_rss_bytes": 900,
                        },
                        "commands": {
                            "decompile_sla": {
                                "returncode": 0,
                                "timeout": False,
                                "elapsed_s": 0.1,
                                "runtime_bucket": "fast",
                                "stdout": benchmark.summarize_text("", include_preview=False),
                                "decompile_quality": {"classification": "structured"},
                                "event": {
                                    "case": "sample",
                                    "command": "decompile_sla",
                                    "repeat_idx": 0,
                                    "temperature": "cold",
                                    "started_at": 1.1,
                                    "ended_at": 1.2,
                                    "elapsed_s": 0.1,
                                },
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
                return cmd_result(batch_stdout, child_max_rss_bytes=100)

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
        self.assertEqual(outputs[0]["resumed_batch_events"][0]["child_max_rss_bytes"], 900)
        self.assertEqual(
            benchmark.aggregate(
                [
                    {
                        "name": "sample",
                        "corpus": "unit",
                        "score": 100,
                        "failures": [],
                        "targets": outputs,
                    }
                ]
            )["memory"]["peak_child_rss_bytes"],
            900,
        )
        flattened = benchmark.collect_command_events([{"targets": outputs}])
        self.assertEqual(
            len([event for event in flattened if event.get("command") == "decompile_sla"]),
            1,
        )
        self.assertEqual(
            len([event for event in flattened if event.get("command") == "case_batch"]),
            2,
        )
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

    def test_collect_command_events_includes_one_shared_case_batch(self):
        shared_batch = {
            "case": "sample",
            "corpus": "unit",
            "target": "sym.a",
            "command": "case_batch",
            "started_at": 1.0,
            "ended_at": 2.0,
            "returncode": 0,
            "child_max_rss_bytes": 4096,
        }
        cases = [
            {
                "targets": [
                    {
                        "batch_event": shared_batch,
                        "command_events": [
                            {"case": "sample", "command": "types", "started_at": 1.1}
                        ],
                    },
                    {
                        "batch_event": {**shared_batch, "target": "sym.b"},
                        "command_events": [
                            {"case": "sample", "command": "profile", "started_at": 1.2}
                        ],
                    },
                ]
            }
        ]

        events = benchmark.collect_command_events(cases)

        self.assertEqual(
            [event["command"] for event in events],
            ["case_batch", "types", "profile"],
        )

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
                    "gold_oracle": {"advisory_mismatches": 0, "expectations": 0},
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

    def test_closure_gate_does_not_promote_source_shape_advisories(self):
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
        self.assertFalse(hasattr(args, "max_gold_failures"))
        self.assertFalse(hasattr(args, "require_gold"))
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
        self.assertFalse(config["raw_output_archive"])
        self.assertIsNone(config["raw_output_archive_root_hash"])

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

    def test_fixed_performance_contract_is_versioned_and_phase0_derived(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )

        self.assertEqual(config["schema"], benchmark.FIXED_PERFORMANCE_GATE_SCHEMA_VERSION)
        self.assertEqual(config["contract"]["target"], "fnv_fold")
        self.assertEqual(config["expected_refusal"]["target"], "mem_scan2")
        self.assertEqual(config["contract"]["cold_samples"], 20)
        self.assertEqual(config["contract"]["warm_sessions"], 4)
        self.assertEqual(config["contract"]["warm_samples_per_session"], 5)
        self.assertEqual(config["contract"]["percentile"], 95)
        self.assertIn("in-process", config["baseline"]["note"])
        self.assertEqual(len(config["contract"]["binary_sha256"]), 64)
        self.assertEqual(
            config["validation_observation"]["runner_fingerprint"]["radare2_abi"],
            132,
        )
        for command_gate in config["gates"]["commands"].values():
            for limit in command_gate.values():
                self.assertGreater(limit["release_target_p95_s"], 0.0)
                self.assertGreater(
                    limit["release_target_p95_s"],
                    limit["reference_p95_s"],
                )
                self.assertEqual(limit["max_regression_ratio"], 1.5)
        for limit in config["gates"]["rss"].values():
            self.assertGreater(
                limit["release_target_p95_bytes"],
                limit["reference_p95_bytes"],
            )
        self.assertEqual(
            config["gates"]["commands"]["decompile_sla"]["cold"][
                "reference_p95_s"
            ],
            config["validation_observation"]["p95"]["decompile_sla"]["cold_s"],
        )

    def test_fixed_performance_gate_passes_complete_measurements(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )
        measurements = {
            "commands": {
                command: {
                    "cold": [
                        min(
                            limit["cold"]["release_target_p95_s"],
                            limit["cold"]["reference_p95_s"],
                        )
                    ]
                    * config["contract"]["cold_samples"],
                    "warm": [
                        min(
                            limit["warm"]["release_target_p95_s"],
                            limit["warm"]["reference_p95_s"],
                        )
                    ]
                    * (
                        config["contract"]["warm_sessions"]
                        * config["contract"]["warm_samples_per_session"]
                    ),
                }
                for command, limit in config["gates"]["commands"].items()
            },
            "rss": {
                "cold": [config["gates"]["rss"]["cold"]["reference_p95_bytes"]]
                * (config["contract"]["cold_samples"] * len(config["contract"]["commands"])),
                "warm": [config["gates"]["rss"]["warm"]["reference_p95_bytes"]]
                * config["contract"]["warm_sessions"],
            },
        }

        gate = benchmark.evaluate_fixed_performance_gate(config, measurements, required=True)

        self.assertEqual(gate["status"], "ok")
        self.assertEqual(gate["failures"], [])
        self.assertLessEqual(
            gate["checks"][
                "commands.decompile_sla.cold.p95_s.regression_vs_reference"
            ]["relative_value"],
            1.0,
        )
        self.assertEqual(
            gate["checks"]["rss.warm.p95_bytes.release_target"]["op"],
            "<=",
        )

    def test_fixed_performance_release_exceedance_does_not_imply_regression(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )
        measurements = {
            "commands": {
                command: {
                    "cold": [limit["cold"]["release_target_p95_s"] * 1.05]
                    * config["contract"]["cold_samples"],
                    "warm": [limit["warm"]["release_target_p95_s"] * 1.05]
                    * (
                        config["contract"]["warm_sessions"]
                        * config["contract"]["warm_samples_per_session"]
                    ),
                }
                for command, limit in config["gates"]["commands"].items()
            },
            "rss": {
                "cold": [config["gates"]["rss"]["cold"]["reference_p95_bytes"]]
                * (config["contract"]["cold_samples"] * len(config["contract"]["commands"])),
                "warm": [config["gates"]["rss"]["warm"]["reference_p95_bytes"]]
                * config["contract"]["warm_sessions"],
            },
        }

        gate = benchmark.evaluate_fixed_performance_gate(config, measurements, required=True)

        metrics = {failure["metric"] for failure in gate["failures"]}
        self.assertEqual(gate["status"], "failed")
        self.assertIn("commands.decompile_sla.cold.p95_s.release_target", metrics)
        self.assertFalse(any("regression_vs_reference" in metric for metric in metrics))

    def test_fixed_performance_gate_reports_absolute_relative_and_rss_failures(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )
        measurements = {
            "commands": {
                command: {
                    "cold": [limit["cold"]["reference_p95_s"]]
                    * config["contract"]["cold_samples"],
                    "warm": [limit["warm"]["reference_p95_s"]]
                    * (
                        config["contract"]["warm_sessions"]
                        * config["contract"]["warm_samples_per_session"]
                    ),
                }
                for command, limit in config["gates"]["commands"].items()
            },
            "rss": {
                "cold": [config["gates"]["rss"]["cold"]["reference_p95_bytes"]]
                * (config["contract"]["cold_samples"] * len(config["contract"]["commands"])),
                "warm": [config["gates"]["rss"]["warm"]["reference_p95_bytes"]]
                * config["contract"]["warm_sessions"],
            },
        }
        measurements["commands"]["decompile_sla"]["cold"] = [10.0] * config["contract"]["cold_samples"]
        measurements["rss"]["warm"] = [600_000_000] * config["contract"]["warm_sessions"]

        gate = benchmark.evaluate_fixed_performance_gate(config, measurements, required=True)

        self.assertEqual(gate["status"], "failed")
        metrics = {failure["metric"] for failure in gate["failures"]}
        self.assertIn("commands.decompile_sla.cold.p95_s.release_target", metrics)
        self.assertIn(
            "commands.decompile_sla.cold.p95_s.regression_vs_reference",
            metrics,
        )
        self.assertIn("rss.warm.p95_bytes.release_target", metrics)
        self.assertIn("rss.warm.p95_bytes.regression_vs_reference", metrics)

    def test_fixed_performance_gate_fails_closed_on_missing_samples(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )

        gate = benchmark.evaluate_fixed_performance_gate(
            config,
            {"commands": {}, "rss": {}},
            required=True,
        )

        self.assertEqual(gate["status"], "failed")
        metrics = {failure["metric"] for failure in gate["failures"]}
        self.assertIn("commands.decompile_sla.cold.samples", metrics)
        self.assertIn("commands.decompile_sla.warm.samples", metrics)
        self.assertIn("rss.cold.samples", metrics)
        self.assertIn("rss.warm.samples", metrics)

    def test_fixed_performance_unavailable_skip_policy_is_explicit(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )
        unavailable = {"status": "unavailable", "reasons": ["fixed runner absent"]}

        optional = benchmark.evaluate_fixed_performance_gate(
            config,
            {},
            availability=unavailable,
            required=False,
        )
        required = benchmark.evaluate_fixed_performance_gate(
            config,
            {},
            availability=unavailable,
            required=True,
        )

        self.assertEqual(optional["status"], "skipped")
        self.assertEqual(optional["failures"], [])
        self.assertEqual(required["status"], "failed")
        self.assertEqual(required["failures"][0]["metric"], "fixed_runner_availability")

    def test_fixed_performance_percentile_uses_nearest_rank(self):
        self.assertEqual(benchmark.fixed_performance_percentile([]), None)
        self.assertEqual(benchmark.fixed_performance_percentile([5, 1, 4, 2, 3]), 5)
        self.assertEqual(
            benchmark.fixed_performance_percentile(list(range(1, 101))),
            95,
        )

    def test_fixed_performance_config_rejects_p95_that_is_the_sample_maximum(self):
        payload = json.loads(
            (ROOT / "tests" / "gold" / "mem_scan2_performance.json").read_text()
        )
        payload["contract"]["cold_samples"] = 15
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "invalid.json"
            path.write_text(json.dumps(payload))
            with self.assertRaisesRegex(ValueError, "non-maximum p95 rank"):
                benchmark.load_fixed_performance_config(path)

    def test_fixed_performance_probe_rejects_stale_abi_and_noop_plugin(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )
        discovery = cmd_result(
            json.dumps([{"name": "sym._fnv_fold", "addr": 0x1000}])
        )
        stale = cmd_result(
            "",
            stderr="WARN: ABI mismatch: Expect 132 vs 131 from anal_sleigh.dylib",
        )
        noop = cmd_result(
            batched_stdout(
                [
                    ("plugin_help", 0, "| pdd - borrowed-snapshot provider"),
                    ("plugin_status", 0, "sla: loaded architecture 'x86'"),
                    ("decompile_sla", 0, ""),
                    ("types", 0, ""),
                    ("profile", 0, ""),
                ]
            )
        )
        healthy = cmd_result(
            batched_stdout(
                [
                    ("plugin_help", 0, "| pdd - borrowed-snapshot provider"),
                    ("plugin_status", 0, "sla: loaded architecture 'x86'"),
                    ("decompile_sla", 0, "int f(void) { return 1; }"),
                    ("types", 0, '{"ret_type":"int","params":[]}'),
                    ("profile", 0, '{"count":1}'),
                ]
            )
        )

        stale_probe = benchmark.fixed_performance_plugin_probe(
            config,
            "r2",
            Path("/tmp/sample"),
            30,
            {},
            mock.Mock(side_effect=[discovery, stale]),
        )
        noop_probe = benchmark.fixed_performance_plugin_probe(
            config,
            "r2",
            Path("/tmp/sample"),
            30,
            {},
            mock.Mock(side_effect=[discovery, noop]),
        )
        healthy_probe = benchmark.fixed_performance_plugin_probe(
            config,
            "r2",
            Path("/tmp/sample"),
            30,
            {},
            mock.Mock(side_effect=[discovery, healthy]),
        )

        self.assertEqual(stale_probe["status"], "failed")
        self.assertTrue(any("ABI/load" in reason for reason in stale_probe["reasons"]))
        self.assertEqual(noop_probe["status"], "failed")
        self.assertTrue(any("no-op" in reason or "empty" in reason for reason in noop_probe["reasons"]))
        self.assertEqual(healthy_probe["status"], "ok")
        self.assertTrue(
            all(item["valid"] for item in healthy_probe["commands"].values())
        )

    def test_fixed_performance_availability_executes_and_requires_abi_probe(self):
        config = benchmark.load_fixed_performance_config(
            ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        )
        args = type(
            "Args",
            (),
            {
                "r2": str(ROOT.parent / "radare2" / "binr" / "radare2" / "radare2"),
                "plugin_dir": str(ROOT / "r2plugin"),
                "tmpdir": "",
                "timeout": 30,
            },
        )()
        failed_probe = {"status": "failed", "reasons": ["stale ABI"]}
        uname = type("Uname", (), {"machine": "arm64"})()
        with (
            mock.patch.object(benchmark.sys, "platform", "darwin"),
            mock.patch.object(benchmark.os, "uname", return_value=uname),
            mock.patch.object(
                benchmark,
                "fixed_performance_plugin_probe",
                return_value=failed_probe,
            ) as probe,
        ):
            availability = benchmark.fixed_performance_availability(
                config,
                args,
                {"R2SLEIGH_FIXED_PERF_RUNNER": "r2sleigh-darwin-arm64-perf-v1"},
            )

        probe.assert_called_once()
        self.assertEqual(availability["status"], "unavailable")
        self.assertIn("plugin ABI/load probe: stale ABI", availability["reasons"])

    def test_fixed_performance_measurements_refuse_noop_or_external_timing(self):
        commands = ("decompile_sla", "types", "profile")
        measurements = {
            "commands": {
                command: {"cold": [], "warm": []} for command in commands
            },
            "rss": {"cold": [], "warm": []},
            "invalid_samples": [],
        }
        target = {
            "commands": {
                "decompile_sla": {
                    "stdout": {"bytes": 0},
                    "decompile_quality": {"classification": "empty"},
                },
                "types": {
                    "stdout": {"bytes": 2},
                    "json_kind": "dict",
                },
                "profile": {
                    "stdout": {"bytes": 11},
                    "json_kind": "dict",
                    "profile_metrics": {"count": 1},
                },
            },
            "command_events": [
                {
                    "command": command,
                    "temperature": "cold",
                    "repeat_idx": 0,
                    "returncode": 0,
                    "timeout": False,
                    "elapsed_s": 0.000001,
                    "timed": command != "profile",
                    "timer": "r2_prof" if command != "profile" else "legacy_or_fallback",
                    "child_max_rss_bytes": 123,
                }
                for command in commands
            ],
        }

        benchmark._record_fixed_performance_target(
            measurements,
            target,
            commands,
            "cold",
        )

        self.assertTrue(
            all(not values["cold"] for values in measurements["commands"].values())
        )
        self.assertEqual(measurements["rss"]["cold"], [])
        self.assertEqual(len(measurements["invalid_samples"]), 3)

    def test_fixed_performance_runner_schedules_cold_and_fresh_warm_sessions(self):
        config_path = ROOT / "tests" / "gold" / "mem_scan2_performance.json"
        config = benchmark.load_fixed_performance_config(config_path)
        commands = tuple(config["contract"]["commands"])

        def target_result(temperature, count, rss):
            events = []
            command_entries = {}
            for command in commands:
                limit = config["gates"]["commands"][command][temperature]
                elapsed = min(
                    limit["reference_p95_s"],
                    limit["release_target_p95_s"],
                )
                for repeat_idx in range(count):
                    event = {
                        "command": command,
                        "temperature": temperature,
                        "repeat_idx": repeat_idx,
                        "returncode": 0,
                        "timeout": False,
                        "elapsed_s": elapsed,
                        "timed": True,
                        "timer": "r2_prof",
                    }
                    if temperature == "cold":
                        event["child_max_rss_bytes"] = rss
                    events.append(event)
                if command == "decompile_sla":
                    command_entries[command] = {
                        "stdout": {"bytes": 24},
                        "decompile_quality": {"classification": "structured"},
                    }
                elif command == "types":
                    command_entries[command] = {
                        "stdout": {"bytes": 24},
                        "json_kind": "dict",
                        "type_metrics": {"ret_type": "int"},
                    }
                elif command == "profile":
                    command_entries[command] = {
                        "stdout": {"bytes": 24},
                        "json_kind": "dict",
                        "profile_metrics": {"count": 1},
                    }
            target = {
                "requested": config["contract"]["target"],
                "command_events": events,
                "commands": command_entries,
            }
            if temperature == "warm":
                target["batch_event"] = {"child_max_rss_bytes": rss}
            return {"targets": [target]}

        cold_result = target_result(
            "cold",
            config["contract"]["cold_samples"],
            config["gates"]["rss"]["cold"]["reference_p95_bytes"],
        )
        warm_results = [
            target_result(
                "warm",
                config["contract"]["warm_samples_per_session"],
                config["gates"]["rss"]["warm"]["reference_p95_bytes"],
            )
            for _ in range(config["contract"]["warm_sessions"])
        ]
        with tempfile.TemporaryDirectory() as tmp:
            args = type(
                "Args",
                (),
                {
                    "fixed_performance_gate": str(config_path),
                    "require_fixed_performance": True,
                    "r2": "r2",
                    "plugin_dir": "r2plugin",
                    "tmpdir": str(Path(tmp) / "runner"),
                    "timeout": 120,
                    "out": str(Path(tmp) / "report.json"),
                },
            )()
            available = {"status": "available", "reasons": []}
            with (
                mock.patch.object(
                    benchmark,
                    "fixed_performance_availability",
                    return_value=available,
                ),
                mock.patch.object(benchmark, "build_r2_env", return_value={}),
                mock.patch.object(
                    benchmark,
                    "run_case",
                    side_effect=[cold_result, *warm_results],
                ) as run_case,
            ):
                exit_code = benchmark.run_fixed_performance_gate(args)

            report = json.loads(Path(args.out).read_text())

        self.assertEqual(exit_code, 0)
        self.assertEqual(report["status"], "ok")
        self.assertEqual(
            report["separation"]["source_shape_diagnostics"],
            "not evaluated; non-authoritative advisory diagnostics run separately",
        )
        self.assertEqual(run_case.call_count, 1 + config["contract"]["warm_sessions"])
        self.assertEqual(
            run_case.call_args_list[0].args[3],
            config["contract"]["cold_samples"],
        )
        self.assertTrue(run_case.call_args_list[0].args[9])
        for call in run_case.call_args_list[1:]:
            self.assertEqual(
                call.args[3],
                config["contract"]["warm_samples_per_session"] + 1,
            )
            self.assertFalse(call.args[9])
        self.assertEqual(
            len(report["measurements"]["commands"]["decompile_sla"]["cold"]),
            config["contract"]["cold_samples"],
        )
        self.assertEqual(
            len(report["measurements"]["commands"]["decompile_sla"]["warm"]),
            config["contract"]["warm_sessions"]
            * config["contract"]["warm_samples_per_session"],
        )
        self.assertEqual(
            len(report["measurements"]["rss"]["warm"]),
            config["contract"]["warm_sessions"],
        )


if __name__ == "__main__":
    unittest.main()
