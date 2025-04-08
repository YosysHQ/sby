#!/usr/bin/env tabbypy3
from __future__ import annotations
import asyncio

import json
import threading
import traceback
import argparse
import shutil
import shlex
import os
import sys
import urllib.parse
import random
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any, Awaitable, Iterable, Literal

try:
    import readline  # type: ignore # noqa
except ImportError:
    pass


libexec = Path(__file__).parent.resolve() / "libexec"

if libexec.exists():
    os.environb[b"PATH"] = bytes(libexec) + b":" + os.environb[b"PATH"]
    sys.path.insert(0, str(libexec))

if True:
    import yosys_mau.task_loop.job_server as job
    from yosys_mau import task_loop as tl
    from yosys_mau.stable_set import StableSet


def safe_smtlib_id(name: str) -> str:
    return f"|{urllib.parse.quote_plus(name).replace('+', ' ')}|"


def arg_parser():
    parser = argparse.ArgumentParser(
        prog="cexenum", usage="%(prog)s [options] <sby_workdir>"
    )

    parser.add_argument(
        "work_dir",
        metavar="<workdir>",
        help="existing SBY work directory",
        type=Path,
    )

    parser.add_argument(
        "--depth",
        type=int,
        metavar="N",
        help="BMC depth for the initial assertion failure (default: %(default)s)",
        default=100,
    )

    parser.add_argument(
        "--enum-depth",
        type=int,
        metavar="N",
        help="number of time steps to run enumeration for, starting with"
        " and including the time step of the first assertion failure"
        " (default: %(default)s)",
        default=10,
    )

    parser.add_argument(
        "--no-sim",
        dest="sim",
        action="store_false",
        help="do not run sim to obtain .fst traces for the enumerated counter examples",
    )

    parser.add_argument(
        "--smtbmc-options",
        metavar='"..."',
        type=shlex.split,
        help='command line options to pass to smtbmc (default: "%(default)s")',
        default="-s yices --unroll",
    )

    parser.add_argument(
        "--callback",
        metavar='"..."',
        type=shlex.split,
        help="command that will receive enumerated traces on stdin and can control "
        "the enumeration via stdout (pass '-' to handle callbacks interactively)",
        default="",
    )

    parser.add_argument(
        "--track-assumes",
        help="track individual assumptions and in case the assumptions cannot be "
        "satisfied, report a subset of used assumptions that are in conflict",
        action="store_true",
    )
    parser.add_argument(
        "--minimize-assumes",
        help="when using --track-assumes, solve for a minimal set of sufficient "
        "assumptions",
        action="store_true",
    )
    parser.add_argument(
        "--satisfy-assumes",
        help="when minimizing counter examples, keep design assumptions satisfied",
        action="store_true",
    )
    parser.add_argument(
        "--diversify",
        help="produce a more diverse set of counter examples early on",
        action="store_true",
    )

    parser.add_argument(
        "--diversify-seed",
        metavar="<N>",
        help="random seed used for --diversify",
        type=int,
        default=1,
    )
    parser.add_argument(
        "--diversify-depth",
        help="stop diversification after enumerating the given number of traces",
        type=int,
    )

    parser.add_argument(
        "--max-per-step",
        metavar="<N>",
        help="advance to the next step after enumerating N traces",
        type=int,
    )

    parser.add_argument("--debug", action="store_true", help="enable debug logging")
    parser.add_argument(
        "--debug-events", action="store_true", help="enable debug event logging"
    )

    parser.add_argument(
        "-j",
        metavar="<N>",
        type=int,
        dest="jobs",
        help="maximum number of processes to run in parallel",
        default=None,
    )

    return parser


def lines(*args: Any):
    return "".join(f"{line}\n" for line in args)


@tl.task_context
class App:
    raw_args: argparse.Namespace

    debug: bool = False
    debug_events: bool = False

    track_assumes: bool = False
    minimize_assumes: bool = False
    satisfy_assumes: bool = False

    depth: int
    enum_depth: int
    sim: bool
    diversify: bool
    diversify_seed: int
    diversify_depth: int | None = None
    max_per_step: int = 0

    callback: list[str]

    smtbmc_options: list[str]

    work_dir: Path

    work_subdir: Path
    trace_dir_full: Path
    trace_dir_min: Path
    cache_dir: Path


def main() -> None:
    args = arg_parser().parse_args()

    job.global_client(args.jobs)

    # Move command line arguments into the App context
    for name in dir(args):
        if name in type(App).__mro__[1].__annotations__:
            setattr(App, name, getattr(args, name))

    App.raw_args = args

    try:
        tl.run_task_loop(task_loop_main)
    except tl.TaskCancelled:
        exit(1)
    except BaseException as e:
        if App.debug or App.debug_events:
            traceback.print_exc()
        tl.log_exception(e, raise_error=False)  # Automatically avoids double logging
        exit(1)


def setup_logging():
    tl.LogContext.app_name = "CEXENUM"
    tl.logging.start_logging()

    if App.debug_events:
        tl.logging.start_debug_event_logging()
    if App.debug:
        tl.LogContext.level = "debug"

    def error_handler(err: BaseException):
        if isinstance(err, tl.TaskCancelled):
            return
        tl.log_exception(err, raise_error=True)

    tl.current_task().set_error_handler(None, error_handler)


async def batch(*args: Awaitable[Any]):
    result = None
    for arg in args:
        if arg is not None:
            result = await arg
    return result


async def task_loop_main() -> None:
    setup_logging()

    cached = False

    App.cache_dir = App.work_dir / "cexenum_cache"
    try:
        App.cache_dir.mkdir()
    except FileExistsError:
        if (App.cache_dir / "done").exists():
            cached = True
        else:
            shutil.rmtree(App.cache_dir)
            App.cache_dir.mkdir()

    App.work_subdir = App.work_dir / "cexenum"
    try:
        App.work_subdir.mkdir()
    except FileExistsError:
        shutil.rmtree(App.work_subdir)
        App.work_subdir.mkdir()

    App.trace_dir_full = App.work_subdir / "full"
    App.trace_dir_full.mkdir()
    App.trace_dir_min = App.work_subdir / "min"
    App.trace_dir_min.mkdir()

    if cached:
        tl.log("Reusing cached AIGER model")
        aig_model = tl.Task()
    else:
        aig_model = AigModel()

    Enumeration(aig_model)


class AigModel(tl.process.Process):
    def __init__(self):
        self[tl.LogContext].scope = "aiger"
        (App.cache_dir / "design_aiger.ys").write_text(
            lines(
                "read_rtlil ../model/design_prep.il",
                "hierarchy -simcheck",
                "flatten",
                "setundef -undriven -anyseq",
                "setattr -set keep 1 w:\\*",
                "delete -output",
                "opt -full",
                "techmap",
                "opt -fast",
                "memory_map -formal",
                "formalff -clk2ff -ff2anyinit",
                "simplemap",
                "dffunmap",
                "abc -g AND -fast",
                "opt_clean",
                "stat",
                "write_rtlil design_aiger.il",
                "write_aiger -I -B -zinit"
                " -map design_aiger.aim -ywmap design_aiger.ywa design_aiger.aig",
            )
        )
        super().__init__(
            ["yosys", "-ql", "design_aiger.log", "design_aiger.ys"], cwd=App.cache_dir
        )
        self.name = "aiger"
        self.log_output()

    async def on_run(self) -> None:
        await super().on_run()
        (App.cache_dir / "done").write_text("")


class MinimizeTrace(tl.Task):
    def __init__(self, trace_name: str, aig_model: tl.Task):
        super().__init__()
        self.trace_name = trace_name

        full_yw = App.trace_dir_full / self.trace_name
        min_yw = App.trace_dir_min / self.trace_name
        min_x_yw = min_yw.with_suffix(".x.yw")

        stem = full_yw.stem

        full_aiw = full_yw.with_suffix(".aiw")
        min_aiw = min_yw.with_suffix(".aiw")

        yw2aiw = YosysWitness(
            "yw2aiw",
            full_yw,
            App.cache_dir / "design_aiger.ywa",
            full_aiw,
            cwd=App.trace_dir_full,
        )
        yw2aiw.depends_on(aig_model)
        yw2aiw[tl.LogContext].scope = f"yw2aiw[{stem}]"

        aigcexmin = AigCexMin(
            App.cache_dir / "design_aiger.aig",
            full_aiw,
            min_aiw,
            cwd=App.trace_dir_min,
        )
        aigcexmin.depends_on(yw2aiw)
        aigcexmin[tl.LogContext].scope = f"aigcexmin[{stem}]"

        self.aiw2yw = aiw2yw = YosysWitness(
            "aiw2yw",
            min_aiw,
            App.cache_dir / "design_aiger.ywa",
            min_yw,
            cwd=App.trace_dir_min,
            options=("--skip-x", "--present-only"),
        )
        aiw2yw[tl.LogContext].scope = f"aiw2yw[{stem}]"
        aiw2yw.depends_on(aigcexmin)

        self.aiw2yw_x = aiw2yw_x = YosysWitness(
            "aiw2yw",
            min_aiw,
            App.cache_dir / "design_aiger.ywa",
            min_x_yw,
            cwd=App.trace_dir_min,
            options=("--present-only",),
        )
        aiw2yw_x[tl.LogContext].scope = f"aiw2yw[{stem}(x)]"
        aiw2yw_x.depends_on(aigcexmin)

        sim = SimTrace(
            App.cache_dir / "design_aiger.il",
            full_yw,
            full_yw.with_suffix(".fst"),
            cwd=App.trace_dir_full,
            script_only=not App.sim,
        )
        sim.depends_on(aig_model)
        sim[tl.LogContext].scope = f"full-sim[{stem}]"

        sim = SimTrace(
            App.cache_dir / "design_aiger.il",
            min_x_yw,
            min_yw.with_suffix(".fst"),
            cwd=App.trace_dir_min,
            script_only=not App.sim,
        )

        sim[tl.LogContext].scope = f"sim[{stem}]"
        sim.depends_on(aiw2yw_x)


def relative_to(target: Path, cwd: Path) -> Path:
    prefix = Path("")
    target = target.resolve()
    cwd = cwd.resolve()

    ok = False
    for limit in (Path.cwd(), App.work_dir):
        limit = Path.cwd().resolve()
        try:
            target.relative_to(limit)
            ok = True
        except ValueError:
            pass
    if not ok:
        return target

    while True:
        try:
            return prefix / (target.relative_to(cwd))
        except ValueError:
            prefix = prefix / ".."
            if cwd == cwd.parent:
                return target
            cwd = cwd.parent


class YosysWitness(tl.process.Process):
    def __init__(
        self,
        mode: Literal["yw2aiw", "aiw2yw"],
        input: Path,
        mapfile: Path,
        output: Path,
        cwd: Path,
        options: Iterable[str] = (),
    ):
        super().__init__(
            [
                "yosys-witness",
                mode,
                *(options or []),
                str(relative_to(input, cwd)),
                str(relative_to(mapfile, cwd)),
                str(relative_to(output, cwd)),
            ],
            cwd=cwd,
        )

        def handler(event: tl.process.OutputEvent):
            tl.log_debug(event.output.rstrip("\n"))

        self.sync_handle_events(tl.process.OutputEvent, handler)


class AigCexMin(tl.process.Process):
    def __init__(self, design_aig: Path, input_aiw: Path, output_aiw: Path, cwd: Path):
        aigcexmin_args = []
        if App.satisfy_assumes:
            aigcexmin_args.append("--satisfy-assumptions")
        super().__init__(
            [
                "aigcexmin",
                *aigcexmin_args,
                str(relative_to(design_aig, cwd)),
                str(relative_to(input_aiw, cwd)),
                str(relative_to(output_aiw, cwd)),
            ],
            cwd=cwd,
        )

        self.log_path = output_aiw.with_suffix(".log")
        self.log_file = None

        def handler(event: tl.process.OutputEvent):
            if self.log_file is None:
                self.log_file = self.log_path.open("w")
            self.log_file.write(event.output)
            self.log_file.flush()
            tl.log_debug(event.output.rstrip("\n"))

        self.sync_handle_events(tl.process.OutputEvent, handler)

    def on_cleanup(self):
        if self.log_file is not None:
            self.log_file.close()
        super().on_cleanup()


class SimTrace(tl.process.Process):
    def __init__(
        self,
        design_il: Path,
        input_yw: Path,
        output_fst: Path,
        cwd: Path,
        script_only: bool = False,
    ):
        self[tl.LogContext].scope = "sim"
        self._script_only = script_only

        script_file = output_fst.with_suffix(".fst.ys")
        log_file = output_fst.with_suffix(".fst.log")

        script_file.write_text(
            lines(
                f"read_rtlil {relative_to(design_il, cwd)}",
                "logger -nowarn"
                ' "Yosys witness trace has an unexpected value for the clock input"',
                f"sim -zinit -r {relative_to(input_yw, cwd)} -hdlname"
                f" -fst {relative_to(output_fst, cwd)}",
            )
        )
        super().__init__(
            [
                "yosys",
                "-ql",
                str(relative_to(log_file, cwd)),
                str(relative_to(script_file, cwd)),
            ],
            cwd=cwd,
        )
        self.name = "sim"
        self.log_output()

    async def on_run(self):
        if self._script_only:
            tl.log(f"manually run {self.shell_command} to generate a full trace")
        else:
            await super().on_run()


class Callback(tl.TaskGroup):
    recover_from_errors = False

    def __init__(self, enumeration: Enumeration):
        super().__init__()
        self[tl.LogContext].scope = "callback"
        self.search_next = False
        self.enumeration = enumeration
        self.tmp_counter = 0

    async def step_callback(self, step: int) -> Literal["advance", "search"]:
        with self.as_current_task():
            return await self._callback(step=step)

    async def unsat_callback(self, step: int) -> Literal["advance", "search"]:
        with self.as_current_task():
            return await self._callback(step=step, unsat=True)

    async def trace_callback(
        self, step: int, path: Path
    ) -> Literal["advance", "search"]:
        with self.as_current_task():
            return await self._callback(step=step, trace_path=path)

    def exit(self):
        pass

    async def _callback(
        self,
        step: int,
        trace_path: Path | None = None,
        unsat: bool = False,
    ) -> Literal["advance", "search"]:
        if not self.is_active():
            if unsat:
                return "advance"
            return "search"
        if trace_path is None and self.search_next:
            if unsat:
                return "advance"
            return "search"
        self.search_next = False

        info = dict(step=step, enabled=sorted(self.enumeration.active_assumptions))

        if trace_path:
            self.callback_write(
                {**info, "event": "trace", "trace_path": str(trace_path)}
            )
        elif unsat:
            self.callback_write({**info, "event": "unsat"})
        else:
            self.callback_write({**info, "event": "step"})

        while True:
            try:
                response: dict[Any, Any] | Any = await self.callback_read()
                if not isinstance(response, (Exception, dict)):
                    raise ValueError(
                        f"expected JSON object, got: {json.dumps(response)}"
                    )
                if isinstance(response, Exception):
                    raise response

                did_something = False

                if "block_yw" in response:
                    did_something = True
                    block_yw: Any = response["block_yw"]

                    if not isinstance(block_yw, str):
                        raise ValueError(
                            "'block_yw' must be a string containing a file path, "
                            f"got: {json.dumps(block_yw)}"
                        )
                    name: Any = response.get("name")
                    if name is not None and not isinstance(name, str):
                        raise ValueError(
                            "optional 'name' must be a string when present, "
                            "got: {json.dumps(name)}"
                        )
                    self.enumeration.block_trace(Path(block_yw), name=name)

                if "block_aiw" in response:
                    did_something = True
                    block_aiw: Any = response["block_aiw"]
                    if not isinstance(block_aiw, str):
                        raise ValueError(
                            "'block_yw' must be a string containing a file path, "
                            f"got: {json.dumps(block_aiw)}"
                        )
                    name: Any = response.get("name")
                    if name is not None and not isinstance(name, str):
                        raise ValueError(
                            "optional 'name' must be a string when present, "
                            "got: {json.dumps(name)}"
                        )

                    tmpdir = App.work_subdir / "tmp"
                    tmpdir.mkdir(exist_ok=True)
                    self.tmp_counter += 1
                    block_yw = tmpdir / f"callback_{self.tmp_counter}.yw"

                    aiw2yw = YosysWitness(
                        "aiw2yw",
                        Path(block_aiw),
                        App.cache_dir / "design_aiger.ywa",
                        Path(block_yw),
                        cwd=tmpdir,
                        options=("--skip-x", "--present-only"),
                    )
                    aiw2yw[tl.LogContext].scope = f"aiw2yw[callback_{self.tmp_counter}]"

                    await aiw2yw.finished
                    self.enumeration.block_trace(Path(block_yw), name=name)

                if "disable" in response:
                    did_something = True
                    name = response["disable"]
                    if not isinstance(name, str):
                        raise ValueError(
                            "'disable' must be a string representing an assumption, "
                            f"got: {json.dumps(name)}"
                        )
                    self.enumeration.disable_assumption(name)
                if "enable" in response:
                    did_something = True
                    name = response["enable"]
                    if not isinstance(name, str):
                        raise ValueError(
                            "'disable' must be a string representing an assumption, "
                            f"got: {json.dumps(name)}"
                        )
                    self.enumeration.enable_assumption(name)
                action: Any = response.get("action")
                if action == "next":
                    did_something = True
                    self.search_next = True
                    action = "search"
                if action in ("search", "advance"):
                    return action
                if not did_something:
                    raise ValueError(
                        f"could not interpret callback response: {response}"
                    )
            except Exception as e:
                tl.log_exception(e, raise_error=False)
                if not self.recover_from_errors:
                    raise

    def is_active(self) -> bool:
        return False

    def callback_write(self, data: Any):
        return

    async def callback_read(self) -> Any:
        raise NotImplementedError("must be implemented in Callback subclass")


class InteractiveCallback(Callback):
    recover_from_errors = True

    interactive_shortcuts = {
        "n": '{"action": "next"}',
        "s": '{"action": "search"}',
        "a": '{"action": "advance"}',
    }

    def __init__(self, enumeration: Enumeration):
        super().__init__(enumeration)
        self.__eof_reached = False

    def is_active(self) -> bool:
        return not self.__eof_reached

    def callback_write(self, data: Any):
        print(f"callback: {json.dumps(data)}")

    async def callback_read(self) -> Any:
        future: asyncio.Future[Any] = asyncio.Future()

        loop = asyncio.get_event_loop()

        def blocking_read():
            try:
                try:
                    result = ""
                    while not result:
                        result = input(
                            "callback> " if sys.stdout.isatty() else ""
                        ).strip()
                    result = self.interactive_shortcuts.get(result, result)
                    result_data = json.loads(result)
                except EOFError:
                    print()
                    self.__eof_reached = True
                    result_data = dict(action="next")
                loop.call_soon_threadsafe(lambda: future.set_result(result_data))
            except Exception as exc:
                exception = exc
                loop.call_soon_threadsafe(lambda: future.set_exception(exception))

        thread = threading.Thread(target=blocking_read, daemon=True)
        thread.start()

        return await future


class ProcessCallback(Callback):
    def __init__(self, enumeration: Enumeration, command: list[str]):
        super().__init__(enumeration)
        self[tl.LogContext].scope = "callback"
        self.__eof_reached = False
        self._command = command
        self._lines: list[asyncio.Future[str]] = [asyncio.Future()]

    def exit(self):
        self.process.close_stdin()

    async def on_prepare(self) -> None:
        self.process = tl.Process(self._command, cwd=Path.cwd(), interact=True)
        self.process.use_lease = False

        future_line: asyncio.Future[str] = self._lines[-1]

        def stdout_handler(event: tl.process.StdoutEvent):
            nonlocal future_line
            future_line.set_result(event.output)
            future_line = asyncio.Future()
            self._lines.append(future_line)

        self.process.sync_handle_events(tl.process.StdoutEvent, stdout_handler)

        def stderr_handler(event: tl.process.StderrEvent):
            tl.log(event.output)

        self.process.sync_handle_events(tl.process.StderrEvent, stderr_handler)

        def exit_handler(event: tl.process.ExitEvent):
            future_line.set_exception(EOFError("callback process exited"))
            # Mark the exception as retrieved
            future_line.exception()

        self.process.sync_handle_events(tl.process.ExitEvent, exit_handler)

    def is_active(self) -> bool:
        return not self.__eof_reached

    def callback_write(self, data: Any):
        if not self.process.is_finished:
            self.process.write(json.dumps(data) + "\n")

    async def callback_read(self) -> Any:
        future_line = self._lines.pop(0)
        try:
            data = json.loads(await future_line)
            tl.log_debug(f"callback action: {data}")
            return data
        except EOFError:
            self._lines.insert(0, future_line)
            self.__eof_reached = True
            return dict(action="next")


def enter_task(fn):
    # TODO move into mau
    import functools

    @functools.wraps(fn)
    def wrapped_fn(self, *args, **kwargs):
        with self.as_current_task():
            return fn(self, *args, **kwargs)

    return wrapped_fn


def inv_signal(sig):
    return (*sig[:-1], "0" if sig[-1] != "0" else "1")


class Diversifier(tl.TaskGroup):
    def __init__(self, seed, enumeration_depth):
        super().__init__()
        self._rng = random.Random(seed)
        self._failed: StableSet[Any] = StableSet()
        self._failed_sets: dict[Any, list[StableSet[Any]]] = defaultdict(list)
        self._active: StableSet[Any] = StableSet()

        self._current_id = 0

        self._targets: dict[int, StableSet[Any]] = {}

        self._sig_index: dict[Any, StableSet[int]] = defaultdict(StableSet)

        self._depth_limit = 0

        self._enumeration_depth_left = enumeration_depth

        self._unsat_counter = 0

        self[tl.LogContext].scope = "diversifier"
        # self[tl.LogContext].level = "debug"

    def _new_id(self):
        self._current_id += 1
        return self._current_id

    @enter_task
    def new_step(self):
        self._failed = StableSet()
        self._failed_sets = defaultdict(list)
        self._active = StableSet()
        self._depth_limit = 0
        self._unsat_counter = 0

    @enter_task
    def diversify(self):
        if self._enumeration_depth_left is not None:
            if self._enumeration_depth_left <= 0:
                return StableSet()

        selected = StableSet()
        blocked = StableSet()

        pending = list(self._targets.values())

        tl.log_debug(f"{len(pending)=} initial")

        depth = 0

        deferred = []
        while pending or (deferred and depth < self._depth_limit):
            if not pending:
                for subspace in deferred:
                    new_subspace = StableSet(
                        sig for sig in subspace if sig[:-1] not in blocked
                    )
                    if new_subspace:
                        pending.append(new_subspace)
                deferred = []
                depth += 1
                continue

            counter = Counter()

            for subspace in self._shuffle_list(pending):
                counter.update(self._shuffle_list(subspace))

            sig, sig_count = max(counter.items(), key=lambda item: item[1])

            tl.log_debug(f"{sig=} {sig_count=}")

            selected.add(sig)
            blocked.add(sig[:-1])

            failed = False

            for candidate in self._failed_sets[sig]:
                if candidate.issubset(selected):
                    failed = True
                    tl.log_debug(f"failed {candidate=}")
                    break

            if not failed:
                for candidate in self._failed_sets[sig]:
                    target = next(s for s in candidate if s not in selected)
                    self._failed_sets[target].append(candidate)

                self._failed_sets.pop(sig, None)

            if failed:
                selected.remove(sig)
                sig = None

            new_pending = []

            for subspace in pending:
                new_subspace = StableSet(
                    sig for sig in subspace if sig[:-1] not in blocked
                )
                if not new_subspace:
                    continue
                if sig in subspace:
                    deferred.append(new_subspace)
                else:
                    new_pending.append(new_subspace)
            pending = new_pending

            tl.log_debug(f"{len(pending)=} {selected=}")

        return selected

    def _add_target(self, signals):
        signals.difference_update(self._failed)
        if signals:
            id = self._new_id()
            self._targets[id] = signals
            for sig in signals:
                self._sig_index[sig].add(id)

    def _remove_target(self, id):
        signals = self._targets.pop(id)
        for sig in signals:
            self._sig_index[sig].remove(id)

    def _remove_target_sig(self, id, sig):
        self._targets[id].remove(sig)
        self._sig_index[sig].remove(id)

    @enter_task
    def update(self, signals):
        if self._enumeration_depth_left is not None:
            if self._enumeration_depth_left > 0:
                self._enumeration_depth_left -= 1
                if self._enumeration_depth_left == 0:
                    tl.log(
                        "reached diversification depth, "
                        "disabling diversification for future traces"
                    )
        self._unsat_counter = 0
        inv_signals = StableSet(map(inv_signal, signals))
        self._add_target(inv_signals)
        self._depth_limit += 1
        tl.log_debug(f"increased {self._depth_limit=}")

    @enter_task
    def failed(self, failed):
        self._unsat_counter += 1
        self._depth_limit = max(0, self._depth_limit - 1)
        tl.log_debug(f"decreased {self._depth_limit=}")

        failed_sig = next(iter(failed))
        self._failed_sets[failed_sig].append(failed)

        if len(failed) == 1:
            self._failed.add(failed_sig)

            for id in list(self._sig_index[failed_sig]):
                self._remove_target_sig(id, failed_sig)

            tl.log(f"found {len(self._failed)} settled inputs")

    def should_minimize(self):
        return self._unsat_counter > 2

    def _shuffle_set(self, items):
        return StableSet(self._shuffle_list(items))

    def _shuffle_list(self, items):
        as_list = list(items)
        self._rng.shuffle(as_list)
        return as_list


def yw_to_dicts(yw_trace):
    """Convert a .yw JSON object to a list of dicts.

    Every item of the list corresponds to one step. For every step it contains a dict
    mapping (*path, index) pairs to the bit value for bits that are present.
    """

    signal_bits = []
    for signal in yw_trace["signals"]:
        chunk_offset = signal["offset"]
        path = tuple(signal["path"])
        for i in range(signal["width"]):
            signal_bits.append((*path, chunk_offset + i))

    return [
        {
            signal: value
            for signal, value in zip(signal_bits, step["bits"][::-1])
            if value in "01"
        }
        for step in yw_trace["steps"]
    ]


class Enumeration(tl.Task):
    callback_mode: Literal["off", "interactive", "process"]
    callback_auto_search: bool = False

    def __init__(self, aig_model: tl.Task):
        self.aig_model = aig_model
        self._pending_blocks: list[tuple[str | None, Path, StableSet[Any] | None]] = []
        self.named_assumptions: StableSet[str] = StableSet()
        self.active_assumptions: StableSet[str] = StableSet()

        self._probes: dict[Any, str] = {}
        self._probe_defs: dict[str, Any] = {}
        if App.diversify:
            self._diversifier = Diversifier(App.diversify_seed, App.diversify_depth)

        self._last_id: int = 0

        super().__init__()

    def _new_id(self) -> int:
        self._last_id += 1
        return self._last_id

    async def on_prepare(self) -> None:
        if App.callback:
            if App.callback == ["-"]:
                self.callback_task = InteractiveCallback(self)
            else:
                self.callback_task = ProcessCallback(self, App.callback)
        else:
            self.callback_task = Callback(self)

    async def on_run(self) -> None:
        self.smtbmc = smtbmc = Smtbmc(App.work_dir / "model" / "design_smt2.smt2")
        self._push_level = 0

        await smtbmc.ping()

        try:
            await self._bmc_loop()
        finally:
            smtbmc.close_stdin()
            self.callback_task.exit()

    async def _bmc_loop(self) -> None:
        smtbmc = self.smtbmc
        i = -1
        limit = App.depth
        first_failure = None

        checked = "skip"

        counter = 0

        while i <= limit or limit < 0:
            if checked != "skip":
                checked = await self._search_counter_example(i)

            if checked == "unsat":
                if i >= 0:
                    action = await self.callback_task.unsat_callback(i)
                    if action == "search":
                        continue
                checked = "skip"
            if checked == "skip":
                checked = "unsat"
                i += 1
                if App.diversify:
                    self._diversifier.new_step()
                if i > limit and limit >= 0:
                    break
                action = await self.callback_task.step_callback(i)

                pending = batch(
                    self._top(),
                    smtbmc.bmc_step(
                        i,
                        initial=i == 0,
                        assertions=False,
                        pred=i - 1 if i else None,
                    ),
                )

                if action == "advance":
                    tl.log(f"Skipping step {i}")
                    await batch(pending, smtbmc.assertions(i))
                    checked = "skip"
                    continue
                assert action == "search"

                tl.log(f"Checking assumptions in step {i}..")
                presat_checked = await batch(
                    pending,
                    smtbmc.check(),
                )
                if presat_checked != "sat":

                    if App.track_assumes:
                        tl.log("No further counter-examples are reachable")

                        tl.log("Conflicting assumptions:")
                        unsat_assumptions = await smtbmc.get_unsat_assumptions(
                            App.minimize_assumes
                        )

                        for key in unsat_assumptions:
                            desc = await smtbmc.incremental_command(
                                cmd="get_design_assume", key=key
                            )
                            if desc is None:
                                tl.log(f"  Callback blocked trace {key[1]!r}")
                                continue
                            expr, path, info = desc
                            tl.log(f"  In {path}: {info}")

                        if not self.active_assumptions:
                            return
                    if first_failure is None and not self.active_assumptions:
                        tl.log_error("Assumptions are not satisfiable")
                    else:
                        tl.log("No further counter-examples are reachable")
                        if not self.active_assumptions:
                            return

                tl.log(f"Checking assertions in step {i}..")
                counter = 0
                continue
            elif checked == "sat":
                if first_failure is None:
                    first_failure = i
                    if App.enum_depth < 0:
                        limit = -1
                    else:
                        limit = i + App.enum_depth
                    tl.log("BMC failed! Enumerating counter-examples..")

                path = App.trace_dir_full / f"trace{i}_{counter}.yw"
                await smtbmc.incremental_command(cmd="write_yw_trace", path=str(path))
                tl.log(f"Written counter-example to {path.name}")

                minimize = MinimizeTrace(path.name, self.aig_model)
                minimize.depends_on(self.aig_model)

                await minimize.aiw2yw.finished

                min_path = App.trace_dir_min / f"trace{i}_{counter}.yw"

                action = await self.callback_task.trace_callback(i, min_path)

                if action == "search" and counter + 1 == App.max_per_step:
                    tl.log(f"Reached trace limit {App.max_per_step} for this step")
                    action = "advance"

                if action == "advance":
                    tl.log("Skipping remaining counter-examples for this step")
                    checked = "skip"
                    continue
                assert action == "search"

                self.block_trace(min_path, diversify=App.diversify)

                counter += 1
            else:
                tl.log_error(f"Unexpected solver result: {checked!r}")

    def block_trace(self, path: Path, name: str | None = None, diversify: bool = False):
        if name is not None:
            if name in self.named_assumptions:
                raise ValueError(f"an assumption with name {name} was already defined")
            self.named_assumptions.add(name)
            self.active_assumptions.add(name)

        self._pending_blocks.append((name, path.absolute(), diversify))

    def enable_assumption(self, name: str):
        if name not in self.named_assumptions:
            raise ValueError(f"unknown assumption {name!r}")
        self.active_assumptions.add(name)

    def disable_assumption(self, name: str):
        if name not in self.named_assumptions:
            raise ValueError(f"unknown assumption {name!r}")
        self.active_assumptions.discard(name)
        self._diversifier.new_step()

    def _top(self) -> Awaitable[Any]:
        return batch(*(self._pop() for _ in range(self._push_level)))

    def _pop(self) -> Awaitable[Any]:
        self._push_level -= 1
        tl.log_debug(f"pop to {self._push_level}")
        return self.smtbmc.pop()

    def _push(self) -> Awaitable[Any]:
        self._push_level += 1
        tl.log_debug(f"push to {self._push_level}")
        return self.smtbmc.push()

    async def _search_counter_example(self, step: int) -> str:
        smtbmc = self.smtbmc
        pending_blocks, self._pending_blocks = self._pending_blocks, []

        pending = self._top()

        add_to_pending = []

        for name, block_path, diversify in pending_blocks:
            result = smtbmc.incremental_command(
                cmd="read_yw_trace",
                name="last",
                path=str(block_path),
                skip_x=True,
            )

            if diversify:

                signals = StableSet(
                    (s, step_signal, value)
                    for s, step_signals in enumerate(
                        yw_to_dicts(json.loads(block_path.read_text()))
                    )
                    for step_signal, value in step_signals.items()
                )

                self._diversifier.update(signals)

            async def check_yw_trace_len():
                last_step = (await result).get("last_step", step)
                if last_step > step:
                    tl.log_warning(
                        f"Ignoring future time steps "
                        f"{step + 1} to {last_step} of "
                        f"{relative_to(block_path, Path.cwd())}"
                    )
                return last_step

            expr = [
                "not",
                ["and", *(["yw", "last", k] for k in range(step + 1))],
            ]

            if name is not None:
                name_id = safe_smtlib_id(f"cexenum trace {name}")
                add_to_pending.append(smtbmc.smtlib(f"(declare-const {name_id} Bool)"))
                expr = ["=", expr, ["smtlib", name_id, "Bool"]]

            add_to_pending.append(check_yw_trace_len())
            add_to_pending.append(smtbmc.assert_(expr))

        active_diversifications = StableSet()

        try:
            while True:
                diversifications = StableSet()
                if App.diversify:

                    diversifications = StableSet(self._diversifier.diversify())

                    for signal_def in active_diversifications.difference(
                        diversifications
                    ):
                        add_to_pending.append(
                            smtbmc.incremental_command(
                                cmd="update_assumptions",
                                key=("cexenum probe", self._probes[signal_def]),
                                expr=None,
                            )
                        )

                    new_probes = False

                    for signal_def in diversifications:
                        if signal_def in self._probes:
                            continue

                        sig_step, (*path, offset), value = signal_def
                        probe_result = smtbmc.incremental_command(
                            cmd="define",
                            expr=[
                                "=",
                                ["yw_sig", sig_step, path, offset],
                                ["bv", value],
                            ],
                        )

                        async def store_probe(signal_def, probe_result):
                            defined = await probe_result
                            self._probes[signal_def] = defined["name"]
                            self._probe_defs[defined["name"]] = signal_def

                        add_to_pending.append(probe_result)
                        add_to_pending.append(store_probe(signal_def, probe_result))
                        new_probes = True

                    if new_probes:
                        await batch(pending, *add_to_pending)
                        pending, add_to_pending = None, []

                    for signal_def in diversifications.difference(
                        active_diversifications
                    ):
                        add_to_pending.append(
                            smtbmc.incremental_command(
                                cmd="update_assumptions",
                                key=("cexenum probe", self._probes[signal_def]),
                                expr=["def", self._probes[signal_def]],
                            )
                        )

                active_diversifications = diversifications

                add_to_pending.append(self._push())
                add_to_pending.append(smtbmc.assertions(step, False))

                for name in self.active_assumptions:
                    name_id = safe_smtlib_id(f"cexenum trace {name}")
                    expr = ["smtlib", name_id, "Bool"]
                    if App.track_assumes:
                        add_to_pending.append(
                            smtbmc.incremental_command(
                                cmd="update_assumptions",
                                key=("cexenum trace", name),
                                expr=expr,
                            )
                        )
                    else:
                        add_to_pending.append(smtbmc.assert_(expr))

                pending = batch(pending, *add_to_pending)

                result = await batch(
                    pending,
                    smtbmc.check(),
                )
                pending, add_to_pending = None, []

                if result == "sat" or not active_diversifications:
                    return result

                failed_assumptions = StableSet(
                    map(
                        tuple,
                        await smtbmc.get_unsat_assumptions(
                            minimize=self._diversifier.should_minimize()
                        ),
                    )
                )

                failed_diversifications = StableSet()

                for key, expr in failed_assumptions:
                    if key == "cexenum probe":
                        failed_diversifications.add(self._probe_defs[expr])

                if failed_diversifications:
                    self._diversifier.failed(failed_diversifications)
                else:
                    return result

                add_to_pending.append(self._top())
        finally:
            for signal_def in active_diversifications:
                add_to_pending.append(
                    smtbmc.incremental_command(
                        cmd="update_assumptions",
                        key=("cexenum probe", self._probes[signal_def]),
                        expr=None,
                    )
                )

            await batch(pending, *add_to_pending)


class Smtbmc(tl.process.Process):
    def __init__(self, smt2_model: Path):
        self[tl.LogContext].scope = "smtbmc"

        smtbmc_options = []
        if App.track_assumes:
            smtbmc_options += ["--track-assumes"]
        if App.minimize_assumes:
            smtbmc_options += ["--minimize-assumes"]
        if App.diversify:
            smtbmc_options += ["--smt2-option", ":produce-unsat-assumptions=true"]

        smtbmc_options += App.smtbmc_options
        super().__init__(
            [
                "yosys-smtbmc",
                "--incremental",
                "--noprogress",
                *smtbmc_options,
                str(smt2_model),
            ],
            interact=True,
        )
        self.name = "smtbmc"

        self.expected_results: list[asyncio.Future[Any]] = []

    async def on_run(self) -> None:
        def output_handler(event: tl.process.StdoutEvent):
            line = event.output.strip()
            if line.startswith("{"):
                result = json.loads(event.output)
            else:
                result = dict(msg=line)
            tl.log_debug(f"smtbmc > {result!r}")
            if "err" in result:
                exception = tl.logging.LoggedError(
                    tl.log_error(result["err"], raise_error=False)
                )
                self.expected_results.pop(0).set_exception(exception)
            if "msg" in result:
                tl.log(result["msg"])
            if "ok" in result:
                assert self.expected_results
                self.expected_results.pop(0).set_result(result["ok"])

        self.sync_handle_events(tl.process.StdoutEvent, output_handler)

        return await super().on_run()

    def ping(self) -> Awaitable[None]:
        return self.incremental_command(cmd="ping")

    def incremental_command(self, **command: Any) -> Awaitable[Any]:
        tl.log_debug(f"smtbmc < {command!r}")
        self.write(json.dumps(command))
        self.write("\n")
        result: asyncio.Future[Any] = asyncio.Future()
        self.expected_results.append(result)

        return result

    def new_step(self, step: int) -> Awaitable[None]:
        return self.incremental_command(cmd="new_step", step=step)

    def push(self) -> Awaitable[None]:
        return self.incremental_command(cmd="push")

    def pop(self) -> Awaitable[None]:
        return self.incremental_command(cmd="pop")

    def check(self) -> Awaitable[str]:
        return self.incremental_command(cmd="check")

    def smtlib(self, command: str, response=False) -> Awaitable[str]:
        return self.incremental_command(
            cmd="smtlib", command=command, response=response
        )

    def assert_antecedent(self, expr: Any) -> Awaitable[None]:
        return self.incremental_command(cmd="assert_antecedent", expr=expr)

    def assert_consequent(self, expr: Any) -> Awaitable[None]:
        return self.incremental_command(cmd="assert_consequent", expr=expr)

    def assert_(self, expr: Any) -> Awaitable[None]:
        return self.incremental_command(cmd="assert", expr=expr)

    def hierarchy(self, step: int) -> Awaitable[None]:
        return self.assert_antecedent(["mod_h", ["step", step]])

    def assert_design_assumes(self, step: int) -> Awaitable[None]:
        return self.incremental_command(cmd="assert_design_assumes", step=step)

    def get_unsat_assumptions(self, minimize: bool) -> Awaitable[list[Any]]:
        return self.incremental_command(cmd="get_unsat_assumptions", minimize=minimize)

    def assumptions(self, step: int, valid: bool = True) -> Awaitable[None]:
        if valid:
            return self.assert_design_assumes(step)

        expr = ["mod_u", ["step", step]]
        if not valid:
            expr = ["not", expr]
        return self.assert_consequent(expr)

    def assertions(self, step: int, valid: bool = True) -> Awaitable[None]:
        expr = ["mod_a", ["step", step]]
        if not valid:
            expr = ["not", expr]
        return self.assert_(expr)

    def initial(self, step: int, initial: bool) -> Awaitable[None]:
        if initial:
            return batch(
                self.assert_antecedent(["mod_i", ["step", step]]),
                self.assert_antecedent(["mod_is", ["step", step]]),
            )
        else:
            return self.assert_antecedent(["not", ["mod_is", ["step", step]]])

    def transition(self, pred: int, succ: int) -> Awaitable[None]:
        return self.assert_antecedent(["mod_t", ["step", pred], ["step", succ]])

    def bmc_step(
        self,
        step: int,
        initial: bool = False,
        assertions: bool = True,
        pred: int | None = None,
        assumptions: bool = True,
    ) -> Awaitable[None]:
        futures: list[Awaitable[None]] = []
        futures.append(self.new_step(step))
        futures.append(self.hierarchy(step))
        if assumptions:
            futures.append(self.assumptions(step))
        futures.append(self.initial(step, initial))

        if pred is not None:
            futures.append(self.transition(pred, step))

        if assertions:
            futures.append(self.assertions(step))

        return batch(*futures)


if __name__ == "__main__":
    main()
