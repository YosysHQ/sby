#!/usr/bin/env tabbypy3
from __future__ import annotations
import asyncio

import json
import traceback
import argparse
import shutil
import shlex
import os
from pathlib import Path
from typing import Any, Awaitable, Literal

import yosys_mau.task_loop.job_server as job
from yosys_mau import task_loop as tl


libexec = Path(__file__).parent.resolve() / "libexec"

if libexec.exists():
    os.environb[b"PATH"] = bytes(libexec) + b":" + os.environb[b"PATH"]


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


def lines(*args):
    return "".join(f"{line}\n" for line in args)


@tl.task_context
class App:
    raw_args: argparse.Namespace

    debug: bool = False
    debug_events: bool = False

    depth: int
    enum_depth: int
    sim: bool

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


async def batch(*args):
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
                "read_rtlil ../model/design_prep.il",
                "hierarchy -simcheck",
                "flatten",
                "setundef -undriven -anyseq",
                "setattr -set keep 1 w:\*",
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
        mode: Literal["yw2aiw"] | Literal["aiw2yw"],
        input: Path,
        mapfile: Path,
        output: Path,
        cwd: Path,
    ):
        super().__init__(
            [
                "yosys-witness",
                mode,
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


class Enumeration(tl.Task):
    def __init__(self, aig_model: tl.Task):
        self.aig_model = aig_model
        super().__init__()

    async def on_run(self) -> None:
        smtbmc = Smtbmc(App.work_dir / "model" / "design_smt2.smt2")

        await smtbmc.ping()

        pred = None

        i = 0
        limit = App.depth
        first_failure = None

        while i <= limit:
            tl.log(f"Checking assumptions in step {i}..")
            presat_checked = await batch(
                smtbmc.bmc_step(i, initial=i == 0, assertions=None, pred=pred),
                smtbmc.check(),
            )
            if presat_checked != "sat":
                if first_failure is None:
                    tl.log_error("Assumptions are not satisfiable")
                else:
                    tl.log("No further counter-examples are reachable")
                    return

            tl.log(f"Checking assertions in step {i}..")
            checked = await batch(
                smtbmc.push(),
                smtbmc.assertions(i, False),
                smtbmc.check(),
            )
            pred = i
            if checked != "unsat":
                if first_failure is None:
                    first_failure = i
                    limit = i + App.enum_depth
                    tl.log("BMC failed! Enumerating counter-examples..")
                counter = 0

                assert checked == "sat"
                path = App.trace_dir_full / f"trace{i}_{counter}.yw"

                while checked == "sat":
                    await smtbmc.incremental_command(
                        cmd="write_yw_trace", path=str(path)
                    )
                    tl.log(f"Written counter-example to {path.name}")

                    minimize = MinimizeTrace(path.name, self.aig_model)
                    minimize.depends_on(self.aig_model)

                    await minimize.aiw2yw.finished

                    min_path = App.trace_dir_min / f"trace{i}_{counter}.yw"

                    checked = await batch(
                        smtbmc.incremental_command(
                            cmd="read_yw_trace",
                            name="last",
                            path=str(min_path),
                            skip_x=True,
                        ),
                        smtbmc.assert_(
                            ["not", ["and", *(["yw", "last", k] for k in range(i + 1))]]
                        ),
                        smtbmc.check(),
                    )

                    counter += 1
                    path = App.trace_dir_full / f"trace{i}_{counter}.yw"

            await batch(smtbmc.pop(), smtbmc.assertions(i))

            i += 1

        smtbmc.close_stdin()


class Smtbmc(tl.process.Process):
    def __init__(self, smt2_model: Path):
        self[tl.LogContext].scope = "smtbmc"
        super().__init__(
            [
                "yosys-smtbmc",
                "--incremental",
                *App.smtbmc_options,
                str(smt2_model),
            ],
            interact=True,
        )
        self.name = "smtbmc"

        self.expected_results = []

    async def on_run(self) -> None:
        def output_handler(event: tl.process.StderrEvent):
            result = json.loads(event.output)
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

    def incremental_command(self, **command: dict[Any]) -> Awaitable[Any]:
        tl.log_debug(f"smtbmc < {command!r}")
        self.write(json.dumps(command))
        self.write("\n")
        result = asyncio.Future()
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
        futures = []
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
