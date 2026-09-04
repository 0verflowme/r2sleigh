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

Two very different things can leave a function with no output, and this adapter
keeps them apart. r2sleigh declining is an answer. The ``r2`` process dying
part-way through the batch is the harness failing to ask, and because the batch
is one process, every function past the cut would otherwise look exactly like a
decline -- which is how five zlib binaries reported zero functions apiece
without anyone reading it as a crash. Those functions are declined with a
``harness:`` cause naming how the process ended and where the stream stopped,
and the run's metadata records the ending of both ``r2`` passes.

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
import signal
import subprocess
import time
from dataclasses import dataclass
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

# radare2 prefixes a function flag with where it learned the name -- `dbg.` from
# debug info, `sym.` from the symbol table, `fcn.` from its own analysis. The
# benchmark matches a decompiled function to its source by name, and
# `dbg.readError` matches nothing, so the prefix comes off. Everything left
# unprefixed keeps whatever radare2 called it.
_FLAG_PREFIXES = ("dbg.", "sym.", "fcn.", "loc.", "flirt.")


def _retitle(code: str, flag: str, source_name: str) -> str:
    """Give the emitted C the source's own name for the function.

    The renderer spells a function after radare2's flag with the characters C
    will not take replaced, so `dbg.readError` is emitted as `dbg_readError`.
    The benchmark parses the C and matches the resulting control-flow graph to
    the source function by name, so leaving the flag's spelling in the code
    means the graph is never matched and the metric is skipped rather than
    scored.
    """
    sanitized = re.sub(r"[^A-Za-z0-9_]", "_", flag)
    if not sanitized or sanitized == source_name:
        return code
    return re.sub(rf"\b{re.escape(sanitized)}\b", source_name, code)


def _source_name(flag: str) -> str:
    """The name the source would use for a radare2 function flag."""
    name = flag
    changed = True
    while changed:
        changed = False
        for prefix in _FLAG_PREFIXES:
            if name.startswith(prefix):
                name = name[len(prefix) :]
                changed = True
    return name or flag


def _r2_bin() -> Path | None:
    explicit = os.environ.get("R2SLEIGH_R2_BIN")
    if explicit:
        candidate = Path(explicit)
        return candidate if candidate.exists() else None
    found = shutil.which("r2") or shutil.which("radare2")
    return Path(found) if found else None


def _signal_name(number: int) -> str:
    """``SIGSEGV`` rather than ``11``; the bare number hides which bug it is."""
    try:
        return signal.Signals(number).name
    except ValueError:
        return "unknown"


def _subprocess_text(value: Any) -> str:
    """Whatever a subprocess handed back, as text, without ever raising.

    ``TimeoutExpired`` carries its partial stdout as *bytes* even under
    ``text=True``: the POSIX reader joins the raw chunks into the exception
    before the decode that text mode would otherwise apply. The stream is also
    cut wherever the kill landed, so it can end mid-character. Replacing rather
    than raising matters here -- output lost to a decode error is exactly the
    evidence this adapter is trying to keep.
    """
    if isinstance(value, str):
        return value
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return ""


@dataclass(frozen=True)
class _R2Run:
    """What one ``r2`` invocation printed, together with how the process ended.

    Handing back bare stdout makes a crash indistinguishable from a quiet run: a
    truncated stream simply has fewer function markers in it, and everything
    past the cut is dropped as though the decompiler had declined it. Carrying
    the exit status alongside the text is what lets a caller tell "r2sleigh had
    nothing to say" from "r2 was not alive to be asked".
    """

    stdout: str
    returncode: int | None
    """``None`` when the process was killed on timeout and so has no status."""
    timeout: float

    @property
    def ended_early(self) -> bool:
        """Whether it finished any way other than a clean exit."""
        return self.returncode != 0

    @property
    def ending(self) -> str:
        """How it finished, in the words the census and metadata should carry."""
        if self.returncode is None:
            return f"timed out after {self.timeout:g}s"
        if self.returncode < 0:
            # POSIX reports a fatal signal as the negated signal number, and the
            # number on its own is not something a reader should have to look
            # up: SIGSEGV and SIGKILL point at very different bugs.
            return f"killed by signal {-self.returncode} ({_signal_name(-self.returncode)})"
        if self.returncode:
            return f"exited {self.returncode}"
        return "completed"


def _run_r2(binary: Path, commands: str, timeout: float) -> _R2Run:
    executable = _r2_bin()
    if executable is None:
        raise RuntimeError("no r2 on PATH and $R2SLEIGH_R2_BIN unset")
    argv = [str(executable), *_R2_FLAGS, "-c", commands, str(binary)]
    try:
        proc = subprocess.run(  # noqa: S603
            argv,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as expired:
        # Letting this propagate loses the whole binary -- its census with it --
        # when the process had in fact answered for most of the batch. Partial
        # output is strictly more informative than none, and it cannot be
        # mistaken for a complete run because the result says how it ended.
        log.warning("r2 timed out after %ss on %s", timeout, binary.name)
        return _R2Run(stdout=_subprocess_text(expired.stdout), returncode=None, timeout=timeout)
    if proc.returncode != 0:
        log.warning("r2 exited %s on %s", proc.returncode, binary.name)
    return _R2Run(stdout=proc.stdout, returncode=proc.returncode, timeout=timeout)


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
            out = _run_r2(Path("/bin/ls"), "a:sla; e asm.arch", timeout=60.0).stdout
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

    def _discover(
        self, binary_path: Path, timeout: float
    ) -> tuple[list[tuple[str, int]], int, _R2Run]:
        """Every function radare2 finds, its address, the load base, and the run.

        The run comes back because an empty function list has two causes that
        look identical from here: a binary radare2 genuinely found nothing in,
        and an `aaa` that never finished. The caller has to be able to say which
        one it is reporting, otherwise the fix for the batch pass just moves the
        silence one step earlier.
        """
        run = _run_r2(binary_path, "a:sla; aaa; e bin.baddr; aflj", timeout=timeout)
        out = run.stdout
        # `e bin.baddr` answers with a bare integer, decimal or `0x`-prefixed,
        # and prints `0` for a position-independent executable.
        baddr = 0
        payload = None
        for line in out.splitlines():
            stripped = line.strip()
            if stripped.startswith("["):
                payload = stripped
                break
            try:
                baddr = int(stripped, 0)
            except ValueError:
                continue
        if payload is None:
            return [], baddr, run
        try:
            functions = json.loads(payload)
        except json.JSONDecodeError:
            return [], baddr, run
        # `aflj` names the entry `addr`; older builds used `offset`.
        return (
            [(f.get("name", ""), int(f.get("addr", f.get("offset", 0)))) for f in functions],
            baddr,
            run,
        )

    #
    # Decompilation
    #

    def decompile_binary(
        self,
        binary_path: Path,
        functions: list[tuple[str, int]] | None = None,
        output_dir: Path | None = None,
        function_names: set[int] | None = None,
        progress_path: Path | None = None,
    ) -> DecompilationResult:
        started = time.time()
        binary_timeout = float(self.config.binary_timeout_seconds)

        discovered, baddr, discovery = self._discover(binary_path, binary_timeout)
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
            # Compare on the source's own name, not radare2's flag. radare2
            # spells a function it learned from DWARF `dbg.slide_hash`, while the
            # benchmark asks for `slide_hash`, so a raw comparison matches
            # nothing and silently discards every candidate -- the binary then
            # reports no functions at all, which reads as a decompiler with
            # nothing to say rather than a filter that removed the work.
            requested = {_source_name(name) for (name, _) in functions}
            candidates = [
                (name, addr) for (name, addr) in candidates
                if _source_name(name) in requested
            ]
        # The benchmark hands a stripped binary and names its own targets by
        # DWARF low_pc, so narrowing is by address, not by symbol.
        narrowed = common.narrow_to_source(
            [(name, to_file_addr(addr)) for (name, addr) in candidates],
            common.addr_targets_of(function_names),
            backend="r2sleigh",
            binary_name=binary_path.name,
        )
        kept = {name for (name, _) in narrowed}
        candidates = [(name, addr) for (name, addr) in candidates if name in kept]

        rendered: dict[str, FunctionDecompilation] = {}
        declined: dict[str, str] = {}
        decompile: _R2Run | None = None
        unreached = 0

        if candidates:
            script = ["a:sla", "aaa"]
            for index, (_, addr) in enumerate(candidates):
                script.append(f"?e {_BEGIN}{index}")
                script.append(f"s {addr}")
                script.append("pdd")
                script.append(f"?e {_END}{index}")
            decompile = _run_r2(binary_path, "; ".join(script), timeout=binary_timeout)

            # Slice once and keep the answers, because where the slices stop is
            # itself the finding. The batch is a single process, so the first
            # function it fails to bracket is where r2 stopped being alive, and
            # every later one is missing for that same reason rather than for
            # anything about its own code -- one cause, named once, counted by
            # how many functions carry it.
            bodies = [_slice(decompile.stdout, index) for index in range(len(candidates))]
            stopped_at = next((i for i, body in enumerate(bodies) if body is None), None)
            harness = ""
            if stopped_at is not None:
                harness = _harness_cause(decompile, stopped_at, len(candidates))

            for index, (name, addr) in enumerate(candidates):
                body = bodies[index]
                if body is None:
                    # Skipping quietly here is the whole defect: it makes a dead
                    # process read as a decompiler with nothing to say. Nothing
                    # was produced, so it is recorded as declined, but with a
                    # cause that says the reason is ours.
                    declined[name] = harness
                    unreached += 1
                    continue
                refusal = _REFUSAL.search(body)
                if refusal is not None:
                    declined[name] = refusal.group("cause")
                    continue
                code = body.strip()
                if not code:
                    continue
                source_name = _source_name(name)
                code = _retitle(code, name, source_name)
                rendered[source_name] = FunctionDecompilation(
                    name=source_name,
                    address=to_file_addr(addr),
                    decompiled_code=code,
                    line_count=len(code.splitlines()),
                    metadata=common.extract_metrics(code),
                )

        # Unconditionally, and after the harness causes have been folded in. A
        # crashed process is the case where the census is most worth having and
        # was previously the one case that never wrote one, because the timeout
        # escaped before this line.
        _write_refusal_census(output_dir, binary_path, declined, len(rendered))

        ended_early = discovery.ended_early or (decompile is not None and decompile.ended_early)

        elapsed = time.time() - started
        return DecompilationResult(
            binary_path=binary_path,
            binary_name=binary_path.stem,
            decompiler=DecompilerMetadata(
                decompiler_name=self.id,
                decompiler_version=self.get_version(),
                total_time_seconds=elapsed,
                extra={
                    "requested": len(candidates),
                    "rendered": len(rendered),
                    "declined": len(declined),
                    "decline_causes": declined,
                    # A sweep is read by comparing its counts against the last
                    # one's, and a count that fell because r2 died means the
                    # opposite of a count that fell because the decompiler got
                    # worse. Both passes report, since a discovery that never
                    # finished yields no candidates at all and would otherwise
                    # be indistinguishable from a binary with no functions.
                    "process_ended_early": ended_early,
                    "process_ending": {
                        "discovery": discovery.ending,
                        "decompile": decompile.ending if decompile is not None else "not run",
                    },
                    "unreached": unreached,
                },
            ),
            functions=rendered,
            output_dir=output_dir,
        )


def _write_refusal_census(
    output_dir: Path | None,
    binary_path: Path,
    declined: dict[str, str],
    rendered: int,
) -> None:
    """Record why each function was declined, beside the run's own results.

    The benchmark keeps a per-function ``decompiled`` boolean and discards
    everything else this adapter learned, so a sweep says *how many* functions
    refused and never *why*. Reading a refusal census off fifty-four corpus
    cells and then prioritising work for a sixteen-hundred-function population
    is how a cause that dominates the wide set stays invisible; this makes the
    wide census a by-product of every sweep instead of a separate exercise.

    Failure to write is deliberately silent. This is measurement about a
    measurement, and it must never be the reason a sweep fails.
    """
    # The benchmark does not always hand the decompiler an output directory, and
    # when it does not, a census that silently declines to write is a census that
    # is never there when it is wanted. Fall back to the binary's own directory,
    # which by construction exists and is inside the run being garbage-collected.
    # The benchmark builds each project in a temporary directory it deletes, so
    # the binary's own parent does not outlive the run and the first fallback
    # wrote a census nobody could read. The harness sets this to a directory
    # inside the run it keeps.
    override = os.environ.get("R2SLEIGH_REFUSAL_CENSUS_DIR")
    if override:
        target = Path(override)
    elif output_dir is not None:
        target = Path(output_dir)
    else:
        target = binary_path.parent
    try:
        counts: dict[str, int] = {}
        for cause in declined.values():
            counts[cause] = counts.get(cause, 0) + 1
        payload = {
            "schema_version": 1,
            "binary": binary_path.name,
            "rendered": rendered,
            "declined": len(declined),
            "causes": dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))),
            "by_function": dict(sorted(declined.items())),
        }
        path = target / f"r2sleigh-refusals-{binary_path.name}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    except OSError:
        return


def _harness_cause(run: _R2Run, stopped_at: int, total: int) -> str:
    """The cause for a function the batch produced no output for at all.

    A refusal is r2sleigh saying it could not prove what the code means; this is
    the harness saying it never got to ask. Spelling them the same way is how
    five zlib binaries reported zero functions each -- 68% of the benchmark's
    refusals -- while looking like an unusually shy decompiler. The `harness:`
    prefix separates the two at a glance in the census, the ending names which
    failure it was, and the stop point says how far the batch got before it
    died; the number of functions carrying the string is the size of the loss.
    """
    if not run.ended_early:
        # A missing marker under a clean exit is a hole rather than a
        # truncation, so it says something swallowed the sentinels, not that r2
        # stopped. Worth a distinct cause: the two want different investigations.
        return "harness: r2 exited cleanly but printed no markers for this function"
    return f"harness: r2 process {run.ending}; output stopped at function {stopped_at} of {total}"


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
