from __future__ import annotations

import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
KERNEL_SMOKE_PATH = ROOT / "scripts" / "kernel_smoke.py"
SPEC = importlib.util.spec_from_file_location("kernel_smoke", KERNEL_SMOKE_PATH)
assert SPEC is not None and SPEC.loader is not None
kernel_smoke = importlib.util.module_from_spec(SPEC)
sys.modules["kernel_smoke"] = kernel_smoke
SPEC.loader.exec_module(kernel_smoke)


def cmd_result(stdout: str, returncode: int = 0, stderr: str = ""):
    return kernel_smoke.CmdResult(
        returncode=returncode,
        stdout=stdout,
        stderr=stderr,
        elapsed_s=0.001,
    )


DISCOVERY_ONE_TARGET = json.dumps(
    [{"name": "sym._IOMalloc", "offset": 0x1000, "nbbs": 2, "size": 32}]
)
VALID_DEC = "int _IOMalloc(void) {\n  return 0;\n}\n"
VALID_JSON = "{}\n"


class KernelSmokeTests(unittest.TestCase):
    def test_parse_json_payload_tolerates_noisy_stdout(self):
        output = "INFO: ignored {not json}\n{\"ok\": true}\nWARN: trailing text\n"
        self.assertEqual(kernel_smoke.parse_json_payload(output), {"ok": True})

    def run_harness(
        self,
        responses: list,
        *,
        targets: str = "_IOMalloc",
        strict: bool = True,
        include_sensitive: bool = False,
    ):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            kernel = tmp_path / "kernelcache.fake"
            kernel.write_bytes(b"not a real kernelcache")
            report = tmp_path / "report.json"
            argv = [
                "kernel_smoke.py",
                "--kernel",
                str(kernel),
                "--r2",
                "radare2",
                "--plugin-dir",
                str(tmp_path / "plugins"),
                "--tmpdir",
                str(tmp_path / "r2tmp"),
                "--targets",
                targets,
                "--out",
                str(report),
            ]
            if strict:
                argv.append("--strict")
            if include_sensitive:
                argv.append("--include-sensitive")
            with mock.patch.object(sys, "argv", argv), mock.patch.object(
                sys, "stdout", new_callable=io.StringIO
            ), mock.patch.object(sys, "stderr", new_callable=io.StringIO), mock.patch.object(
                kernel_smoke, "run_r2", side_effect=responses
            ) as run_r2:
                exit_code = kernel_smoke.main()
            return exit_code, json.loads(report.read_text()), run_r2.call_args_list, str(kernel)

    def valid_target_responses(self) -> list:
        return [
            cmd_result(DISCOVERY_ONE_TARGET),
            cmd_result(VALID_DEC),
            cmd_result(VALID_DEC),
            cmd_result(VALID_DEC),
            cmd_result(VALID_JSON),
            cmd_result(VALID_JSON),
            cmd_result(VALID_JSON),
        ]

    def test_strict_fails_missing_target(self):
        exit_code, report, calls, _ = self.run_harness(
            [cmd_result(DISCOVERY_ONE_TARGET)], targets="_Missing"
        )

        self.assertEqual(exit_code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual([failure["kind"] for failure in report["failures"]], ["missing_target"])
        self.assertEqual(calls[0].args[2], "a:sla >/dev/null; aaaa; aflj")
        self.assertEqual(len(calls), 1)

    def test_strict_fails_zero_discovered_functions(self):
        exit_code, report, _, _ = self.run_harness([cmd_result("[]\n")])

        self.assertEqual(exit_code, 1)
        self.assertEqual(report["discovery"]["function_count"], 0)
        self.assertIn("zero_functions", {failure["kind"] for failure in report["failures"]})
        self.assertIn("missing_target", {failure["kind"] for failure in report["failures"]})

    def test_strict_fails_malformed_json_outputs(self):
        responses = [
            cmd_result(DISCOVERY_ONE_TARGET),
            cmd_result(VALID_DEC),
            cmd_result(VALID_DEC),
            cmd_result(VALID_DEC),
            cmd_result("not json\n"),
            cmd_result("also not json\n"),
            cmd_result(""),
        ]
        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 1)
        json_failures = [
            (failure["kind"], failure["command"]) for failure in report["failures"]
        ]
        self.assertIn(("json_parse", "types"), json_failures)
        self.assertIn(("json_parse", "profile"), json_failures)
        self.assertIn(("json_parse", "symex"), json_failures)

    def test_strict_fails_decompiler_fallback_text(self):
        responses = self.valid_target_responses()
        responses[1] = cmd_result("/* r2dec fallback: skipped decompilation */\n")
        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 1)
        self.assertIn(
            ("decompiler_fallback", "decompile_sla"),
            {(failure["kind"], failure.get("command")) for failure in report["failures"]},
        )
        self.assertEqual(
            report["targets"][0]["commands"]["decompile_sla"]["fallback_marker"],
            "r2dec fallback:",
        )

    def test_budget_refusal_is_not_hard_decompiler_fallback(self):
        responses = self.valid_target_responses()
        responses[1] = cmd_result(
            "/* r2dec budget: skipped decompilation for main (2198 blocks > limit 200). */\n"
        )
        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 0)
        self.assertEqual(report["failures"], [])
        self.assertNotIn(
            "fallback_marker",
            report["targets"][0]["commands"]["decompile_sla"],
        )

    def test_strict_fails_command_return_failure(self):
        responses = self.valid_target_responses()
        responses[2] = cmd_result("boom\n", returncode=7)
        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 1)
        self.assertIn(
            ("command_return", "decompile_pdd", 7),
            {
                (failure["kind"], failure.get("command"), failure.get("returncode"))
                for failure in report["failures"]
            },
        )

    def test_report_redacts_kernel_path_and_previews_by_default(self):
        responses = self.valid_target_responses()
        responses[1] = cmd_result("local path preview should hide\n")
        exit_code, report, _, kernel_path = self.run_harness(responses, strict=False)
        report_text = json.dumps(report, sort_keys=True)

        self.assertEqual(exit_code, 0)
        self.assertEqual(report["kernel"], "<redacted:kernelcache.fake>")
        self.assertNotIn(kernel_path, report_text)
        self.assertNotIn("local path preview should hide", report_text)
        self.assertNotIn("preview", report["targets"][0]["commands"]["decompile_sla"]["stdout"])

    def test_report_can_include_sensitive_previews_for_local_triage(self):
        responses = self.valid_target_responses()
        responses[1] = cmd_result("local preview\n")
        exit_code, report, _, kernel_path = self.run_harness(
            responses, strict=False, include_sensitive=True
        )

        self.assertEqual(exit_code, 0)
        self.assertEqual(report["kernel"], kernel_path)
        self.assertEqual(
            report["targets"][0]["commands"]["decompile_sla"]["stdout"]["preview"],
            ["local preview"],
        )


if __name__ == "__main__":
    unittest.main()
