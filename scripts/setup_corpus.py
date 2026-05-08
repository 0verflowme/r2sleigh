#!/usr/bin/env python3
"""Local corpus builder for r2sleigh reversing benchmarks.

All downloads, source trees, build output, and manifests live under
`/tmp/r2sleigh-corpora` by default. The script is intentionally conservative:
Coreutils is the first deterministic tier, while larger corpora are skipped
unless explicitly enabled or already present locally.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import time
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Optional


SCHEMA_VERSION = 1
DEFAULT_ROOT = Path("/tmp/r2sleigh-corpora")
DEFAULT_MANIFEST = "manifest.json"
GNU_COREUTILS_INDEX = "https://ftp.gnu.org/gnu/coreutils/"
GNU_COREUTILS_PRIORITY = ("ls", "cp", "sort", "wc", "sha256sum", "dd")
SECONDARY_TIERS = frozenset({"cgc", "juliet"})
JULIET_HINT_URL = "https://samate.nist.gov/SARD/test-suites/112National?page=2350"
CGC_REPO_URL = "https://github.com/GrammaTech/cgc-cbs.git"


@dataclass(frozen=True)
class CommandResult:
    argv: tuple[str, ...]
    returncode: int
    elapsed_s: float
    stdout: str = ""
    stderr: str = ""


Runner = Callable[[list[str], Optional[Path], Optional[dict[str, str]], int], CommandResult]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build or inspect local corpora for scripts/reversing_benchmark.py."
    )
    parser.add_argument(
        "mode",
        choices=("setup", "manifest", "clean"),
        help="setup corpora, write manifest from current corpus root, or remove the corpus root",
    )
    parser.add_argument(
        "--root",
        default=str(DEFAULT_ROOT),
        help="local corpus root; defaults to /tmp/r2sleigh-corpora",
    )
    parser.add_argument(
        "--tier",
        action="append",
        choices=("coreutils", "cgc", "juliet", "all"),
        default=[],
        help="corpus tier to operate on; may be repeated; default is coreutils",
    )
    parser.add_argument(
        "--manifest-out",
        default="",
        help="manifest path; defaults to ROOT/manifest.json",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="plan actions without downloading, building, or deleting",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="allow clean on non-default roots and rebuild existing outputs",
    )
    parser.add_argument(
        "--allow-large-downloads",
        action="store_true",
        help="allow CGC/Juliet network fetches; coreutils is always allowed",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="parallel build jobs for supported corpora",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1800,
        help="per build/download command timeout in seconds",
    )
    parser.add_argument(
        "--coreutils-version",
        default="latest",
        help="coreutils version or 'latest'",
    )
    parser.add_argument(
        "--max-functions",
        type=int,
        default=6,
        help="per-binary benchmark target cap written to manifest entries",
    )
    parser.add_argument(
        "--include-sensitive",
        action="store_true",
        help="write absolute local paths and command previews in the manifest",
    )
    return parser.parse_args()


def selected_tiers(raw: list[str]) -> list[str]:
    values = raw or ["coreutils"]
    if "all" in values:
        values = ["coreutils", "cgc", "juliet"]
    out: list[str] = []
    for value in values:
        if value not in out:
            out.append(value)
    return out


def redacted_path(path: Path) -> str:
    return f"<redacted:{path.name}>"


def display_path(path: Path, include_sensitive: bool) -> str:
    return str(path) if include_sensitive else redacted_path(path)


def is_executable(path: Path) -> bool:
    try:
        return path.is_file() and os.access(path, os.X_OK)
    except OSError:
        return False


def run_command(
    argv: list[str],
    cwd: Path | None,
    env: dict[str, str] | None,
    timeout_s: int,
) -> CommandResult:
    start = time.perf_counter()
    proc = subprocess.run(
        argv,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout_s,
        check=False,
    )
    return CommandResult(
        argv=tuple(argv),
        returncode=proc.returncode,
        elapsed_s=time.perf_counter() - start,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )


def tool_exists(name: str) -> bool:
    return shutil.which(name) is not None


def version_key(version: str) -> tuple[int, ...]:
    return tuple(int(part) for part in re.findall(r"\d+", version))


def find_latest_coreutils_archive(index_html: str) -> tuple[str, str] | None:
    matches = re.findall(r'href="(coreutils-([0-9][0-9.]+)\.tar\.xz)"', index_html)
    if not matches:
        return None
    archive, version = max(matches, key=lambda item: version_key(item[1]))
    return archive, version


def download_url(url: str, dest: Path, *, dry_run: bool) -> dict[str, Any]:
    if dry_run:
        return {"action": "download", "url": url, "path": str(dest), "dry_run": True}
    dest.parent.mkdir(parents=True, exist_ok=True)
    with urllib.request.urlopen(url, timeout=120) as response:
        data = response.read()
    dest.write_bytes(data)
    return {"action": "download", "url": url, "path": str(dest), "bytes": len(data)}


def fetch_text(url: str) -> str:
    with urllib.request.urlopen(url, timeout=120) as response:
        return response.read().decode("utf-8", "replace")


def safe_extract_tar(archive: Path, dest: Path, *, dry_run: bool) -> dict[str, Any]:
    if dry_run:
        return {"action": "extract", "archive": str(archive), "dest": str(dest), "dry_run": True}
    dest.mkdir(parents=True, exist_ok=True)
    root = dest.resolve()
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        for member in members:
            target = (dest / member.name).resolve()
            if root != target and root not in target.parents:
                raise ValueError(f"unsafe archive path: {member.name}")
        tar.extractall(dest)
    return {"action": "extract", "archive": str(archive), "dest": str(dest)}


def command_step(result: CommandResult, include_sensitive: bool) -> dict[str, Any]:
    item: dict[str, Any] = {
        "argv": list(result.argv) if include_sensitive else [Path(result.argv[0]).name, "..."],
        "returncode": result.returncode,
        "elapsed_s": round(result.elapsed_s, 6),
    }
    if include_sensitive:
        if result.stdout.strip():
            item["stdout_preview"] = result.stdout.splitlines()[:20]
        if result.stderr.strip():
            item["stderr_preview"] = result.stderr.splitlines()[:20]
    return item


def binary_entry(
    path: Path,
    corpus: str,
    include_sensitive: bool,
    *,
    targets: list[str] | None = None,
    analysis: str = "aaa",
    max_functions: int = 6,
) -> dict[str, Any]:
    return {
        "name": path.name,
        "path": str(path) if include_sensitive else str(path),
        "display_path": display_path(path, include_sensitive),
        "corpus": corpus,
        "analysis": analysis,
        "targets": targets or [],
        "max_functions": max_functions,
    }


def skip_entry(corpus: str, reason: str) -> dict[str, str]:
    return {"corpus": corpus, "reason": reason}


def build_coreutils(
    root: Path,
    version: str,
    jobs: int,
    timeout_s: int,
    max_functions: int,
    include_sensitive: bool,
    dry_run: bool,
    force: bool,
    runner: Runner = run_command,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    steps: list[dict[str, Any]] = []
    skips: list[dict[str, Any]] = []
    downloads = root / "downloads"
    sources = root / "src"
    core_root = root / "coreutils"
    try:
        if version == "latest":
            if dry_run:
                archive_name, resolved_version = ("coreutils-latest.tar.xz", "latest")
            else:
                latest = find_latest_coreutils_archive(fetch_text(GNU_COREUTILS_INDEX))
                if latest is None:
                    skips.append(skip_entry("coreutils", "could not discover latest GNU coreutils tarball"))
                    return [], steps, skips
                archive_name, resolved_version = latest
        else:
            resolved_version = version
            archive_name = f"coreutils-{version}.tar.xz"
        archive = downloads / archive_name
        src_parent = sources / "coreutils"
        src_dir = src_parent / f"coreutils-{resolved_version}"
        url = f"{GNU_COREUTILS_INDEX}{archive_name}"
        if force and not dry_run:
            shutil.rmtree(src_dir, ignore_errors=True)
        if not archive.exists():
            steps.append(download_url(url, archive, dry_run=dry_run))
        if not src_dir.exists():
            steps.append(safe_extract_tar(archive, src_parent, dry_run=dry_run))
        if dry_run:
            return [
                binary_entry(
                    core_root / "bin" / name,
                    "coreutils",
                    include_sensitive,
                    max_functions=max_functions,
                )
                for name in GNU_COREUTILS_PRIORITY
            ], steps, skips
        if not (src_dir / "Makefile").exists():
            env = os.environ.copy()
            env["FORCE_UNSAFE_CONFIGURE"] = "1"
            configure = runner(
                [
                    "./configure",
                    "--disable-nls",
                    "--enable-single-binary=no",
                    f"--prefix={core_root / 'install'}",
                ],
                src_dir,
                env,
                timeout_s,
            )
            steps.append(command_step(configure, include_sensitive))
            if configure.returncode != 0:
                skips.append(skip_entry("coreutils", "configure failed"))
                return [], steps, skips
        existing_entries = [
            binary_entry(src_dir / "src" / name, "coreutils", include_sensitive, max_functions=max_functions)
            for name in GNU_COREUTILS_PRIORITY
            if is_executable(src_dir / "src" / name)
        ]
        if len(existing_entries) == len(GNU_COREUTILS_PRIORITY) and not force:
            return existing_entries, steps, skips
        make = runner(["make", f"-j{max(1, jobs)}"], src_dir, os.environ.copy(), timeout_s)
        steps.append(command_step(make, include_sensitive))
        if make.returncode != 0:
            skips.append(skip_entry("coreutils", "make failed"))
        entries: list[dict[str, Any]] = []
        for name in GNU_COREUTILS_PRIORITY:
            path = src_dir / "src" / name
            if is_executable(path):
                entries.append(
                    binary_entry(path, "coreutils", include_sensitive, max_functions=max_functions)
                )
            else:
                skips.append(skip_entry("coreutils", f"missing executable {name}"))
        return entries, steps, skips
    except Exception as exc:  # noqa: BLE001 - manifesting deterministic skip reason is the product behavior.
        skips.append(skip_entry("coreutils", f"{type(exc).__name__}: {exc}"))
        return [], steps, skips


def scan_existing_binaries(root: Path, corpus: str, include_sensitive: bool, limit: int = 32) -> list[dict[str, Any]]:
    if corpus == "coreutils":
        roots = [root / "coreutils", root / "src" / "coreutils"]
    else:
        roots = [root / corpus]
    paths: list[Path] = []
    for corpus_root in roots:
        if not corpus_root.exists():
            continue
        paths.extend(path for path in corpus_root.rglob("*") if is_executable(path))
    if not paths:
        return []
    paths = sorted(
        paths,
        key=lambda path: str(path),
    )
    return [binary_entry(path, corpus, include_sensitive) for path in paths[:limit]]


def setup_secondary_tier(
    root: Path,
    corpus: str,
    allow_large_downloads: bool,
    include_sensitive: bool,
    dry_run: bool,
    timeout_s: int,
    runner: Runner = run_command,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    existing = scan_existing_binaries(root, corpus, include_sensitive)
    if existing:
        return existing, [], []
    if not allow_large_downloads:
        return [], [], [skip_entry(corpus, "not present locally; pass --allow-large-downloads to fetch")]
    if corpus == "cgc":
        if not tool_exists("git"):
            return [], [], [skip_entry("cgc", "git is not installed")]
        repo_dir = root / "cgc" / "src" / "cgc-cbs"
        if dry_run:
            return [], [{"action": "git-clone", "url": CGC_REPO_URL, "path": str(repo_dir), "dry_run": True}], []
        repo_dir.parent.mkdir(parents=True, exist_ok=True)
        steps: list[dict[str, Any]] = []
        if not repo_dir.exists():
            clone = runner(["git", "clone", "--depth=1", CGC_REPO_URL, str(repo_dir)], None, None, timeout_s)
            steps.append(command_step(clone, include_sensitive))
            if clone.returncode != 0:
                return [], steps, [skip_entry("cgc", "git clone failed")]
        entries = scan_existing_binaries(root, "cgc", include_sensitive)
        if not entries:
            return [], steps, [skip_entry("cgc", "no native ELF outputs found; DECREE-only cases skipped")]
        return entries, steps, []
    if corpus == "juliet":
        return [], [], [
            skip_entry(
                "juliet",
                f"download discovery requires NIST SARD archive resolution from {JULIET_HINT_URL}",
            )
        ]
    return [], [], [skip_entry(corpus, "unknown secondary corpus")]


def manifest_payload(
    root: Path,
    tiers: list[str],
    binaries: list[dict[str, Any]],
    skips: list[dict[str, Any]],
    steps: list[dict[str, Any]],
    include_sensitive: bool,
) -> dict[str, Any]:
    binaries_sorted = sorted(
        binaries,
        key=lambda item: (str(item.get("corpus", "")), str(item.get("name", "")), str(item.get("path", ""))),
    )
    skips_sorted = sorted(skips, key=lambda item: (str(item.get("corpus", "")), str(item.get("reason", ""))))
    return {
        "schema": SCHEMA_VERSION,
        "root": str(root) if include_sensitive else redacted_path(root),
        "tiers": tiers,
        "binaries": binaries_sorted,
        "skips": skips_sorted,
        "steps": steps,
    }


def write_manifest(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def current_manifest(root: Path, tiers: list[str], include_sensitive: bool) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    binaries: list[dict[str, Any]] = []
    skips: list[dict[str, Any]] = []
    for tier in tiers:
        found = scan_existing_binaries(root, tier, include_sensitive)
        binaries.extend(found)
        if not found:
            skips.append(skip_entry(tier, "no local binaries found"))
    return binaries, skips


def clean_root(root: Path, dry_run: bool, force: bool) -> dict[str, Any]:
    resolved = root.resolve()
    default_parent = DEFAULT_ROOT.parent.resolve()
    if not force and (resolved.parent != default_parent or not resolved.name.startswith("r2sleigh-corpora")):
        raise ValueError(f"refusing to clean non-default corpus root without --force: {resolved}")
    if dry_run:
        return {"action": "clean", "root": str(resolved), "dry_run": True}
    shutil.rmtree(resolved, ignore_errors=True)
    return {"action": "clean", "root": str(resolved)}


def run_setup(args: argparse.Namespace, runner: Runner = run_command) -> dict[str, Any]:
    root = Path(args.root)
    tiers = selected_tiers(args.tier)
    all_binaries: list[dict[str, Any]] = []
    all_steps: list[dict[str, Any]] = []
    all_skips: list[dict[str, Any]] = []
    for tier in tiers:
        if tier == "coreutils":
            binaries, steps, skips = build_coreutils(
                root,
                args.coreutils_version,
                args.jobs,
                args.timeout,
                args.max_functions,
                args.include_sensitive,
                args.dry_run,
                args.force,
                runner=runner,
            )
        elif tier in SECONDARY_TIERS:
            binaries, steps, skips = setup_secondary_tier(
                root,
                tier,
                args.allow_large_downloads,
                args.include_sensitive,
                args.dry_run,
                args.timeout,
                runner=runner,
            )
        else:
            binaries, steps, skips = [], [], [skip_entry(tier, "unknown tier")]
        all_binaries.extend(binaries)
        all_steps.extend(steps)
        all_skips.extend(skips)
    return manifest_payload(root, tiers, all_binaries, all_skips, all_steps, args.include_sensitive)


def main() -> int:
    args = parse_args()
    root = Path(args.root)
    tiers = selected_tiers(args.tier)
    manifest_out = Path(args.manifest_out) if args.manifest_out else root / DEFAULT_MANIFEST
    if args.mode == "clean":
        payload = {
            "schema": SCHEMA_VERSION,
            "root": str(root) if args.include_sensitive else redacted_path(root),
            "steps": [clean_root(root, args.dry_run, args.force)],
        }
        write_manifest(manifest_out, payload)
        print(f"corpus clean {'planned' if args.dry_run else 'complete'}; wrote {manifest_out}")
        return 0
    if args.mode == "manifest":
        binaries, skips = current_manifest(root, tiers, args.include_sensitive)
        payload = manifest_payload(root, tiers, binaries, skips, [], args.include_sensitive)
    else:
        payload = run_setup(args)
    write_manifest(manifest_out, payload)
    print(
        "corpus "
        f"{args.mode}; tiers={','.join(tiers)} binaries={len(payload.get('binaries', []))} "
        f"skips={len(payload.get('skips', []))} wrote {manifest_out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
