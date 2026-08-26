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
VALID_PAYLOAD = {
    "schema_version": 2,
    "entry": 0x1000,
    "entry_hex": "0x1000",
    "num_blocks": 1,
    "blocks": [
        {
            "addr": 0x1000,
            "addr_hex": "0x1000",
            "size": 4,
            "phis": [],
            "ops": [],
        }
    ],
    "prepared": {
        "formal_parameters": [],
        "parameter_addresses": [],
    },
}
VALID_JSON = json.dumps(VALID_PAYLOAD)


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
        ]

    def test_smoke_runs_decompile_and_ssa_report_probes_in_order(self):
        exit_code, report, calls, _ = self.run_harness(self.valid_target_responses())

        self.assertEqual(exit_code, 0)
        self.assertEqual(
            set(report["targets"][0]["commands"]),
            {
                "decompile_sla",
                "decompile_pdd",
                "decompile_pdD",
                "ssa_function_report",
            },
        )
        self.assertEqual(
            [call.args[2].rsplit("; ", 1)[-1] for call in calls[1:]],
            ["pdd", "pdd", "pdD", "a:sla.debug.ssa.func"],
        )
        self.assertIs(
            report["targets"][0]["commands"]["ssa_function_report"]["ssa_report_valid"],
            True,
        )

    def test_strict_fails_invalid_ssa_function_report(self):
        responses = self.valid_target_responses()
        payload = {**VALID_PAYLOAD, "num_blocks": 0, "blocks": []}
        responses[-1] = cmd_result(json.dumps(payload))

        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 1)
        self.assertIn(
            "invalid_ssa_function_report",
            {failure["kind"] for failure in report["failures"]},
        )

    def test_strict_fails_ssa_report_for_another_target(self):
        responses = self.valid_target_responses()
        payload = {**VALID_PAYLOAD, "entry": 0x2000, "entry_hex": "0x2000"}
        responses[-1] = cmd_result(json.dumps(payload))

        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 1)
        self.assertIn(
            "invalid_ssa_function_report",
            {failure["kind"] for failure in report["failures"]},
        )

    def test_strict_fails_missing_future_or_wrong_type_ssa_report_schema(self):
        def without(key):
            return {name: value for name, value in VALID_PAYLOAD.items() if name != key}

        invalid_payloads = (
            (without("schema_version"), "missing"),
            ({**VALID_PAYLOAD, "schema_version": 3}, "future"),
            ({**VALID_PAYLOAD, "schema_version": "2"}, "wrong type"),
        )
        for payload, label in invalid_payloads:
            with self.subTest(label=label):
                responses = self.valid_target_responses()
                responses[-1] = cmd_result(json.dumps(payload))

                exit_code, report, _, _ = self.run_harness(responses)

                self.assertEqual(exit_code, 1)
                self.assertIn(
                    "invalid_ssa_function_report",
                    {failure["kind"] for failure in report["failures"]},
                )

    def test_strict_fails_missing_wrong_or_noop_ssa_report_shapes(self):
        def without(key):
            return {name: value for name, value in VALID_PAYLOAD.items() if name != key}

        def block(**changes):
            return {
                **VALID_PAYLOAD,
                "blocks": [{**VALID_PAYLOAD["blocks"][0], **changes}],
            }

        def block_without(key):
            item = {
                name: value
                for name, value in VALID_PAYLOAD["blocks"][0].items()
                if name != key
            }
            return {**VALID_PAYLOAD, "blocks": [item]}

        def prepared(**changes):
            return {
                **VALID_PAYLOAD,
                "prepared": {**VALID_PAYLOAD["prepared"], **changes},
            }

        def prepared_without(key):
            facts = {
                name: value
                for name, value in VALID_PAYLOAD["prepared"].items()
                if name != key
            }
            return {**VALID_PAYLOAD, "prepared": facts}

        invalid_payloads = (
            ({}, "no-op object"),
            (without("entry"), "missing entry"),
            ({**VALID_PAYLOAD, "entry": True}, "wrong entry type"),
            (without("entry_hex"), "missing entry_hex"),
            ({**VALID_PAYLOAD, "entry_hex": "0x2000"}, "wrong entry_hex"),
            (without("num_blocks"), "missing num_blocks"),
            ({**VALID_PAYLOAD, "num_blocks": 2}, "block-count mismatch"),
            (without("blocks"), "missing blocks"),
            ({**VALID_PAYLOAD, "blocks": [{}]}, "no-op block"),
            (block(addr="0x1000"), "wrong block addr type"),
            (block(addr_hex="0x2000"), "wrong block addr_hex"),
            (block_without("size"), "missing block size"),
            (block(size=0), "non-positive block size"),
            (block(phis={}), "wrong phis type"),
            (block(ops={}), "wrong ops type"),
            (
                block(addr=0x2000, addr_hex="0x2000"),
                "missing entry block",
            ),
            (without("prepared"), "missing prepared"),
            ({**VALID_PAYLOAD, "prepared": {}}, "no-op prepared"),
            (
                prepared_without("formal_parameters"),
                "missing formal parameters",
            ),
            (prepared(formal_parameters={}), "wrong formal parameters type"),
            (
                prepared_without("parameter_addresses"),
                "missing parameter addresses",
            ),
            (prepared(parameter_addresses={}), "wrong parameter addresses type"),
        )
        for payload, label in invalid_payloads:
            with self.subTest(label=label):
                responses = self.valid_target_responses()
                responses[-1] = cmd_result(json.dumps(payload))

                exit_code, report, _, _ = self.run_harness(responses)

                self.assertEqual(exit_code, 1)
                command = report["targets"][0]["commands"]["ssa_function_report"]
                self.assertIs(command["ssa_report_valid"], False)
                self.assertIn(
                    "invalid_ssa_function_report",
                    {failure["kind"] for failure in report["failures"]},
                )

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
        ]
        exit_code, report, _, _ = self.run_harness(responses)

        self.assertEqual(exit_code, 1)
        json_failures = [
            (failure["kind"], failure["command"]) for failure in report["failures"]
        ]
        self.assertEqual(
            json_failures,
            [("json_parse", "ssa_function_report")],
        )

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
