"""Raw r2sleigh backend (native, via the ``r2`` CLI).

r2sleigh (https://github.com/0verflowme/r2sleigh) is a radare2 plugin whose
decompiler is a Rust pipeline: Ghidra Sleigh lift -> its own IL -> SSA -> machine
projection -> a sealed binding plan -> C rendering. It is a *refusal-first*
decompiler: where it cannot prove what a construct means it emits a typed
refusal instead of plausible C, so a function is either rendered or reported as
declined, never guessed.

Like ``glaurung`` and ``kuna`` it is driven as a CLI rather than imported, but
unlike them the CLI is radare2 itself. One ``r2`` process per binary does the
whole job::

    r2 -e scr.color=0 -q -c 'a:sla; aaa; <per-function seek and pdd>' <binary>

``a:sla`` swaps radare2's architecture plugin for the Sleigh-backed one, which
is what makes ``pdd`` render r2sleigh's output rather than the stock r2dec one,
so it must run before analysis. Functions are marked in the stream with
``R2SLEIGH_DECBENCH_BEGIN__<index>`` / ``..._END__<index>`` sentinels and split
back out here; one process amortises the ``aaa`` that dominates the wall time.

Discovery comes from radare2's own analysis (``aflj``), so this works on
stripped binaries, and addresses are normalised the way the dockerized r2dec
driver does it -- ``addr - baddr + elf_min_vaddr`` -- because radare2 loads at
its own ``baddr``.

A declined function is *omitted* rather than emitted as its refusal comment.
Scoring a refusal marker as if it were decompiled C would report a parse failure
where the tool actually reported an honest decline, and both are zero on every
metric anyway; the counts are kept in the result metadata so the decline rate
stays visible.

Locate the CLI via ``$R2SLEIGH_R2_BIN`` (an explicit ``r2`` path) or ``r2`` on
``$PATH``. The plugin itself must already be installed into radare2's plugin
directory (``make -C r2plugin install`` in the r2sleigh tree); availability is
probed by checking that ``a:sla`` actually switches the architecture.
"""

from __future__ import annotations

import json
import logging
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any

from decbench.decompilers.base import Decompiler, DecompilerConfig
from decbench.decompilers.raw import common
from decbench.decompilers.registry import register_decompiler
from decbench.models.decompilation import (
    DecompilationResult,
    DecompilerMetadata,
    FunctionDecompilation,
)

log = logging.getLogger(__name__)

_BEGIN = "R2SLEIGH_DECBENCH_BEGIN__"
_END = "R2SLEIGH_DECBENCH_END__"

# What the plugin prints when it declines a function. The text carries the typed
# cause, which is worth keeping in metadata even though the function is dropped.
_REFUSAL = re.compile(r"/\* r2dec fallback: skipped decompilation for \S+ \((?P<cause>.*)\) \*/")

_R2_FLAGS = ("-e", "scr.color=0", "-e", "bin.relocs.apply=true", "-q")


def _r2_bin() -> Path | None:
    explicit = os.environ.get("R2SLEIGH_R2_BIN")
    if explicit:
        candidate = Path(explicit)
        return candidate if candidate.exists() else None
    found = shutil.which("r2") or shutil.which("radare2")
    return Path(found) if found else None


def _run_r2(binary: Path, commands: str, timeout: float) -> str:
    executable = _r2_bin()
    if executable is None:
        raise RuntimeError("no r2 on PATH and $R2SLEIGH_R2_BIN unset")
    proc = subprocess.run(  # noqa: S603
        [str(executable), *_R2_FLAGS, "-c", commands, str(binary)],
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )
    return proc.stdout


@register_decompiler("r2sleigh")
class RawR2SleighDecompiler(Decompiler):
    """r2sleigh (Sleigh-lifted, refusal-first) driven through the r2 CLI."""

    name = "r2sleigh"
    display_name = "r2sleigh"

    def __init__(self, config: DecompilerConfig | None = None):
        super().__init__(config)
        self._version_value: str | None = None
        self._version_probed = False

    #
    # Decompiler interface
    #

    def is_available(self) -> bool:
        if _r2_bin() is None:
            return False
        # The plugin is what we are benchmarking, not radare2: probe that
        # `a:sla` actually swaps the architecture rather than that r2 exists.
        try:
            out = _run_r2(Path("/bin/ls"), "a:sla; e asm.arch", timeout=60.0)
        except Exception:  # noqa: BLE001
            return False
        return "sla: loaded architecture" in out or "sleigh" in out.lower()

    def get_version(self) -> str | None:
        if self._version_probed:
            return self._version_value
        self._version_probed = True
        executable = _r2_bin()
        if executable is None:
            return None
        try:
            proc = subprocess.run(  # noqa: S603
                [str(executable), "-v"], capture_output=True, text=True, timeout=30, check=False
            )
            first = proc.stdout.strip().splitlines()[0] if proc.stdout.strip() else ""
        except Exception:  # noqa: BLE001
            first = ""
        self._version_value = f"r2sleigh via {first}" if first else "r2sleigh"
        return self._version_value

    #
    # Discovery
    #

    def _discover(self, binary_path: Path, timeout: float) -> tuple[list[tuple[str, int]], int]:
        """Every function radare2 finds, with its address and the load base."""
        out = _run_r2(binary_path, "a:sla; aaa; e bin.baddr; aflj", timeout=timeout)
        baddr = 0
        payload = None
        for line in out.splitlines():
            stripped = line.strip()
            if stripped.startswith("["):
                payload = stripped
                break
            if stripped.startswith("0x") and baddr == 0:
                with_prefix = stripped
                try:
                    baddr = int(with_prefix, 16)
                except ValueError:
                    baddr = 0
        if payload is None:
            return [], baddr
        try:
            functions = json.loads(payload)
        except json.JSONDecodeError:
            return [], baddr
        return [(f.get("name", ""), int(f.get("offset", 0))) for f in functions], baddr

    #
    # Decompilation
    #

    def decompile_binary(
        self,
        binary_path: Path,
        functions: list[tuple[str, int]] | None = None,
        output_dir: Path | None = None,
    ) -> DecompilationResult:
        started = time.time()
        binary_timeout = float(self.config.binary_timeout_seconds)

        discovered, baddr = self._discover(binary_path, binary_timeout)
        min_vaddr = common.elf_min_vaddr(binary_path)
        text_range = common.elf_text_ranges(binary_path)

        def to_file_addr(addr: int) -> int:
            return addr - baddr + min_vaddr

        candidates = [
            (name, addr)
            for (name, addr) in discovered
            if not common.should_skip_function(name, to_file_addr(addr), text_range)
        ]
        if functions is not None:
            wanted = common.addr_targets_of({addr for (_, addr) in functions})
            candidates = [
                (name, addr) for (name, addr) in candidates if to_file_addr(addr) in wanted
            ]

        rendered: dict[str, FunctionDecompilation] = {}
        declined: dict[str, str] = {}

        if candidates:
            script = ["a:sla", "aaa"]
            for index, (_, addr) in enumerate(candidates):
                script.append(f"?e {_BEGIN}{index}")
                script.append(f"s {addr}")
                script.append("pdd")
                script.append(f"?e {_END}{index}")
            out = _run_r2(binary_path, "; ".join(script), timeout=binary_timeout)

            for index, (name, addr) in enumerate(candidates):
                body = _slice(out, index)
                if body is None:
                    continue
                refusal = _REFUSAL.search(body)
                if refusal is not None:
                    declined[name] = refusal.group("cause")
                    continue
                code = body.strip()
                if not code:
                    continue
                rendered[name] = FunctionDecompilation(
                    name=name,
                    address=to_file_addr(addr),
                    decompiled_code=code,
                    line_count=len(code.splitlines()),
                    metadata=common.extract_metrics(code),
                )

        elapsed = time.time() - started
        return DecompilationResult(
            binary_path=binary_path,
            binary_name=binary_path.stem,
            decompiler=DecompilerMetadata(
                decompiler_name=self.id,
                decompiler_version=self.get_version(),
                total_time_seconds=elapsed,
            ),
            functions=rendered,
            output_dir=output_dir,
            metadata={
                "requested": len(candidates),
                "rendered": len(rendered),
                "declined": len(declined),
                "decline_causes": declined,
            },
        )


def _slice(out: str, index: int) -> str | None:
    """The text one function's markers enclose."""
    begin = out.find(f"{_BEGIN}{index}")
    if begin < 0:
        return None
    begin = out.find("\n", begin)
    if begin < 0:
        return None
    end = out.find(f"{_END}{index}", begin)
    if end < 0:
        return None
    return out[begin + 1 : end]
