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
from pathlib import Path
from typing import Any, Awaitable, Iterable, Literal

try:
    import readline  # type: ignore # noqa
except ImportError:
    pass

import yosys_mau.task_loop.job_server as job
from yosys_mau import task_loop as tl
from yosys_mau.stable_set import StableSet


libexec = Path(__file__).parent.resolve() / "libexec"

if libexec.exists():
    os.environb[b"PATH"] = bytes(libexec) + b":" + os.environb[b"PATH"]


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

    depth: int
    enum_depth: int
    sim: bool

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
                "read_ilang ../model/design_prep.il",
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

        if App.sim:
            sim = SimTrace(
                App.cache_dir / "design_aiger.il",
                min_yw,
                min_yw.with_suffix(".fst"),
                cwd=App.trace_dir_min,
            )

            sim[tl.LogContext].scope = f"sim[{stem}]"
            sim.depends_on(aiw2yw)


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
        super().__init__(
            [
                "aigcexmin",
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
    def __init__(self, design_il: Path, input_yw: Path, output_fst: Path, cwd: Path):
        self[tl.LogContext].scope = "sim"

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
            self._lines[-1].set_exception(EOFError("callback process exited"))

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


class Enumeration(tl.Task):
    callback_mode: Literal["off", "interactive", "process"]
    callback_auto_search: bool = False

    def __init__(self, aig_model: tl.Task):
        self.aig_model = aig_model
        self._pending_blocks: list[tuple[str | None, Path]] = []
        self.named_assumptions: StableSet[str] = StableSet()
        self.active_assumptions: StableSet[str] = StableSet()

        super().__init__()

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
                if i > limit and limit >= 0:
                    break
                action = await self.callback_task.step_callback(i)

                pending = batch(
                    self._top(),
                    smtbmc.bmc_step(
                        i, initial=i == 0, assertions=None, pred=i - 1 if i else None
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
                    if first_failure is None:
                        tl.log_error("Assumptions are not satisfiable")
                    else:
                        tl.log("No further counter-examples are reachable")
                        smtbmc.close_stdin()
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
                if action == "advance":
                    tl.log("Skipping remaining counter-examples for this step")
                    checked = "skip"
                    continue
                assert action == "search"

                self.block_trace(min_path)

                counter += 1
            else:
                tl.log_error(f"Unexpected solver result: {checked!r}")
        smtbmc.close_stdin()

    def block_trace(self, path: Path, name: str | None = None):
        if name is not None:
            if name in self.named_assumptions:
                raise ValueError(f"an assumption with name {name} was already defined")
            self.named_assumptions.add(name)
            self.active_assumptions.add(name)

        self._pending_blocks.append((name, path.absolute()))

    def enable_assumption(self, name: str):
        if name not in self.named_assumptions:
            raise ValueError(f"unknown assumption {name!r}")
        self.active_assumptions.add(name)

    def disable_assumption(self, name: str):
        if name not in self.named_assumptions:
            raise ValueError(f"unknown assumption {name!r}")
        self.active_assumptions.discard(name)

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

    def _search_counter_example(self, step: int) -> Awaitable[Any]:
        smtbmc = self.smtbmc
        pending_blocks, self._pending_blocks = self._pending_blocks, []

        pending = self._top()

        for name, block_path in pending_blocks:
            result = smtbmc.incremental_command(
                cmd="read_yw_trace",
                name="last",
                path=str(block_path),
                skip_x=True,
            )

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
                pending = batch(
                    pending, smtbmc.smtlib(f"(declare-const {name_id} Bool)")
                )
                expr = ["=", expr, ["smtlib", name_id, "Bool"]]

            pending = batch(
                pending,
                check_yw_trace_len(),
                smtbmc.assert_(expr),
            )

        pending = batch(
            pending,
            self._push(),
            smtbmc.assertions(step, False),
        )

        for name in self.active_assumptions:
            name_id = safe_smtlib_id(f"cexenum trace {name}")
            pending = batch(pending, smtbmc.assert_(["smtlib", name_id, "Bool"]))

        return batch(
            pending,
            smtbmc.check(),
        )


class Smtbmc(tl.process.Process):
    def __init__(self, smt2_model: Path):
        self[tl.LogContext].scope = "smtbmc"
        super().__init__(
            [
                "yosys-smtbmc",
                "--incremental",
                "--noprogress",
                *App.smtbmc_options,
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

    def smtlib(self, command: str) -> Awaitable[str]:
        return self.incremental_command(cmd="smtlib", command=command)

    def assert_antecedent(self, expr: Any) -> Awaitable[None]:
        return self.incremental_command(cmd="assert_antecedent", expr=expr)

    def assert_consequent(self, expr: Any) -> Awaitable[None]:
        return self.incremental_command(cmd="assert_consequent", expr=expr)

    def assert_(self, expr: Any) -> Awaitable[None]:
        return self.incremental_command(cmd="assert", expr=expr)

    def hierarchy(self, step: int) -> Awaitable[None]:
        return self.assert_antecedent(["mod_h", ["step", step]])

    def assumptions(self, step: int, valid: bool = True) -> Awaitable[None]:
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
        assertions: bool | None = True,
        pred: int | None = None,
    ) -> Awaitable[None]:
        futures: list[Awaitable[None]] = []
        futures.append(self.new_step(step))
        futures.append(self.hierarchy(step))
        futures.append(self.assumptions(step))
        futures.append(self.initial(step, initial))

        if pred is not None:
            futures.append(self.transition(pred, step))

        if assertions is not None:
            futures.append(self.assertions(assertions))

        return batch(*futures)


if __name__ == "__main__":
    main()
