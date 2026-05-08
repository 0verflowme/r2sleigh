from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SETUP_PATH = ROOT / "scripts" / "setup_corpus.py"
SPEC = importlib.util.spec_from_file_location("setup_corpus", SETUP_PATH)
assert SPEC is not None and SPEC.loader is not None
setup_corpus = importlib.util.module_from_spec(SPEC)
sys.modules["setup_corpus"] = setup_corpus
SPEC.loader.exec_module(setup_corpus)


class SetupCorpusTests(unittest.TestCase):
    def test_find_latest_coreutils_archive_uses_highest_version(self):
        html = "\n".join(
            [
                '<a href="coreutils-9.4.tar.xz">coreutils-9.4.tar.xz</a>',
                '<a href="coreutils-10.1.tar.xz">coreutils-10.1.tar.xz</a>',
                '<a href="coreutils-9.10.tar.xz">coreutils-9.10.tar.xz</a>',
            ]
        )

        self.assertEqual(
            setup_corpus.find_latest_coreutils_archive(html),
            ("coreutils-10.1.tar.xz", "10.1"),
        )

    def test_setup_dry_run_writes_deterministic_coreutils_manifest_shape(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = Namespace(
                root=tmp,
                tier=["coreutils"],
                coreutils_version="latest",
                jobs=1,
                timeout=1,
                include_sensitive=False,
                dry_run=True,
                force=False,
                allow_large_downloads=False,
                max_functions=6,
            )

            first = setup_corpus.run_setup(args)
            second = setup_corpus.run_setup(args)

        self.assertEqual(first, second)
        self.assertEqual(first["tiers"], ["coreutils"])
        self.assertEqual(len(first["binaries"]), len(setup_corpus.GNU_COREUTILS_PRIORITY))
        self.assertEqual(first["skips"], [])

    def test_secondary_tier_skips_without_large_downloads(self):
        with tempfile.TemporaryDirectory() as tmp:
            entries, steps, skips = setup_corpus.setup_secondary_tier(
                Path(tmp),
                "cgc",
                allow_large_downloads=False,
                include_sensitive=False,
                dry_run=False,
                timeout_s=1,
            )

        self.assertEqual(entries, [])
        self.assertEqual(steps, [])
        self.assertEqual(skips[0]["corpus"], "cgc")
        self.assertIn("--allow-large-downloads", skips[0]["reason"])

    def test_manifest_mode_scans_only_requested_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "coreutils" / "bin" / "ls"
            binary.parent.mkdir(parents=True)
            binary.write_text("#!/bin/sh\n")
            binary.chmod(0o755)

            binaries, skips = setup_corpus.current_manifest(root, ["coreutils", "juliet"], False)

        self.assertEqual([item["name"] for item in binaries], ["ls"])
        self.assertEqual(skips, [{"corpus": "juliet", "reason": "no local binaries found"}])

    def test_clean_refuses_non_default_root_without_force(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):
                setup_corpus.clean_root(Path(tmp), dry_run=True, force=False)

    def test_write_manifest_is_stable_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "manifest.json"
            payload = {"schema": 1, "binaries": [{"name": "b"}, {"name": "a"}]}

            setup_corpus.write_manifest(path, payload)
            loaded = json.loads(path.read_text())

        self.assertEqual(loaded, payload)


if __name__ == "__main__":
    unittest.main()
