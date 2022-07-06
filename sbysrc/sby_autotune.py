#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import os
import re
import subprocess
from shutil import rmtree, which
from time import monotonic
from sby_core import SbyAbort, SbyTask


class SbyAutotuneConfig:
    """Autotune configuration parsed from the sby file or an external autotune config
    file.
    """
    def __init__(self):
        self.timeout = None
        self.soft_timeout = 60
        self.wait_percentage = 50
        self.wait_seconds = 10
        self.parallel = "auto"

        self.presat = None
        self.incr = "auto"
        self.incr_threshold = 20
        self.mem = "auto"
        self.mem_threshold = 10240
        self.forall = "auto"

    def config_line(self, log, line, file_kind="sby file"):
        option, *arg = line.split(None, 1)
        if not arg:
            log.error(f"{file_kind} syntax error: {line}")
        arg = arg[0].strip()

        BOOL_OR_ANY = {"on": True, "off": False, "any": None}
        BOOL_ANY_OR_AUTO = {"on": True, "off": False, "any": None, "auto": "auto"}
        ON_ANY_OR_AUTO = {"on": True, "any": None, "auto": "auto"}

        def enum_option(values):
            if arg not in values:
                values_str = ', '.join(repr(value) for value in sorted(values))
                log.error(f"{file_kind}: invalid value '{arg}' for autotune option {option}, valid values are: {values_str}")
            return values[arg]

        def int_option():
            try:
                return int(arg)
            except ValueError:
                log.error(f"{file_kind}: invalid value '{arg}' for autotune option {option}, expected an integer value")

        if option == "timeout":
            self.timeout = "none" if arg == "none" else int_option()
        elif option == "soft_timeout":
            self.soft_timeout = int_option()
        elif option == "wait":
            self.wait_percentage = 0
            self.wait_seconds = 0
            for part in arg.split("+"):
                part = part.strip()
                if part.endswith("%"):
                    self.wait_percentage += int(part[:-1].strip())
                else:
                    self.wait_seconds += int(part)
        elif option == "parallel":
            self.parallel = "auto" if arg == "auto" else int_option()
        elif option == "presat":
            self.presat = enum_option(BOOL_OR_ANY)
        elif option == "incr":
            self.incr = enum_option(BOOL_ANY_OR_AUTO)
        elif option == "incr_threshold":
            self.incr_threshold = int_option()
        elif option == "mem":
            self.mem = enum_option(ON_ANY_OR_AUTO)
        elif option == "mem_threshold":
            self.mem_threshold = int_option()
        elif option == "forall":
            self.forall = enum_option(ON_ANY_OR_AUTO)
        else:
            log.error(f"{file_kind} syntax error: {line}")

    def parse_file(self, log, file):
        for line in file:
            line = re.sub(r"\s*(\s#.*)?$", "", line)
            if line == "" or line[0] == "#":
                continue
            self.config_line(log, line.rstrip(), "autotune configuration file")

class SbyAutotuneCandidate:
    """An engine configuration to try and its current state during autotuning.
    """
    def __init__(self, autotune, engine):
        self.autotune = autotune
        self.engine = engine

        self.state = "pending"
        self.engine_idx = None
        self.info = f"{' '.join(self.engine)}:"
        self.suspended = 0
        self.suspend = 1

        self.engine_retcode = None
        self.engine_status = None
        self.total_adjusted_time = None

        self.soft_timeout = self.autotune.config.soft_timeout

        if tuple(self.engine) not in self.autotune.candidate_engines:
            self.autotune.active_candidates.append(self)
            self.autotune.candidate_engines.add(tuple(self.engine))

    def set_engine_idx(self, idx):
        self.engine_idx = idx
        self.info = f"engine_{idx} ({' '.join(self.engine)}):"

    def set_running(self):
        assert not self.suspended
        assert self.state == "pending"
        assert self in self.autotune.active_candidates
        self.state = "running"

    def retry_later(self):
        assert self.state == "running"
        assert self in self.autotune.active_candidates
        self.state = "pending"
        self.soft_timeout *= 2
        self.suspended = self.suspend

    def timed_out(self):
        assert self.state == "running"
        self.autotune.active_candidates.remove(self)
        self.state = "timeout"

    def failed(self):
        assert self.state == "running"
        self.autotune.active_candidates.remove(self)
        self.autotune.failed_candidates.append(self)
        self.state = "failed"

    def finished(self):
        assert self.state == "running"
        self.autotune.active_candidates.remove(self)
        self.autotune.finished_candidates.append(self)
        self.state = "finished"

    def threads(self):
        if self.autotune.config.mode == "prove" and self.engine[0] == "smtbmc":
            return 2
        return 1


class SbyAutotune:
    """Performs automatic engine selection for a given task.
    """
    def __init__(self, task, config_file=None):
        self.task_exit_callback = task.exit_callback
        task.exit_callback = lambda: None
        task.check_timeout = lambda: None
        task.status = "TIMEOUT"
        task.retcode = 8

        task.proc_failed = self.proc_failed

        self.config = None

        if config_file:
            with open(config_file) as config:
                self.config.parse_file(task, config)

        self.task = task

        self.done = False
        self.threads_running = 0

        self.next_engine_idx = 0

        self.model_requests = {}

        self.timeout = None
        self.best_time = None
        self.have_pending_candidates = False

        self.active_candidates = []
        self.finished_candidates = []
        self.failed_candidates = []

        self.candidate_engines = set()

    def available(self, tool):
        if not which(tool):
            return False

        if tool == "btorsim":
            error_msg = subprocess.run(
                ["btorsim", "--vcd"],
                capture_output=True,
                text=True,
            ).stderr
            if "invalid command line option" in error_msg:
                self.log('found version of "btorsim" is too old and does not support the --vcd option')
                return False

        return True

    def candidate(self, *engine):
        flat_engine = []
        def flatten(part):
            if part is None:
                return
            elif isinstance(part, (tuple, list)):
                for subpart in part:
                    flatten(subpart)
            else:
                flat_engine.append(part)

        flatten(engine)

        SbyAutotuneCandidate(self, flat_engine)

    def configure(self):
        self.config.mode = self.task.opt_mode
        self.config.skip = self.task.opt_skip

        if self.config.incr == "auto":
            self.config.incr = None
            if self.config.mode != "live":
                steps = self.task.opt_depth - (self.config.skip or 0)
                if steps > self.config.incr_threshold:
                    self.log(f"checking more than {self.config.incr_threshold} timesteps ({steps}), disabling nonincremental smtbmc")
                    self.config.incr = True

        if self.config.mem == "auto":
            self.config.mem = None
            if self.task.design is None:
                self.log("warning: unknown amount of memory bits in design")
            elif self.task.design.memory_bits > self.config.mem_threshold:
                self.log(
                    f"more than {self.config.mem_threshold} bits of memory in design ({self.task.design.memory_bits} bits), "
                    "disabling engines without native memory support"
                )
                self.config.mem = True

        if self.config.forall == "auto":
            self.config.forall = None
            if self.task.design.forall:
                self.log("design uses $allconst/$allseq, disabling engines without forall support")
                self.config.forall = True

        if self.config.mode not in ["bmc", "prove"]:
            self.config.presat = None

        if self.config.parallel == "auto":
            try:
                self.config.parallel = len(os.sched_getaffinity(0))
            except AttributeError:
                self.config.parallel = os.cpu_count()  # TODO is this correct?

        if self.config.timeout is None:
            self.config.timeout = self.task.opt_timeout
        elif self.config.timeout == "none":
            self.config.timeout = None

    def build_candidates(self):
        if self.config.mode == "live":
            # Not much point in autotuning here...
            self.candidate("aiger", "suprove")
            return

        if self.config.presat is None:
            presat_flags = [None, "--nopresat"]
        elif self.config.presat:
            presat_flags = [None]
        else:
            presat_flags = ["--nopresat"]

        if self.config.incr is None:
            noincr_flags = [None, ["--", "--noincr"]]
        elif self.config.incr:
            noincr_flags = [None]
        else:
            noincr_flags = [["--", "--noincr"]]

        if self.config.forall:
            self.log('disabling engines "smtbmc boolector" and "smtbmc bitwuzla" as they do not support forall')
        else:
            for solver in ["boolector", "bitwuzla"]:
                if not self.available(solver):
                    self.log(f'disabling engine "smtbmc {solver}" as the solver "{solver}" was not found')
                    continue
                for noincr in noincr_flags:
                    for presat in presat_flags:
                        self.candidate("smtbmc", presat, solver, noincr)

        if not self.available("btorsim"):
            self.log('disabling engine "btor" as the "btorsim" tool was not found')
        elif self.config.forall:
            self.log('disabling engine "btor" as it does not support forall')
        else:
            if self.config.mode in ["bmc", "cover"]:
                if not self.available("btormc"):
                    self.log('disabling engine "btor btormc" as the "btormc" tool was not found')
                elif self.config.presat:
                    self.log('disabling engine "btor btormc" as it does not support presat checking')
                else:
                    self.candidate("btor", "btormc")

            if self.config.mode == "bmc":
                if not self.available("pono"):
                    self.log('disabling engine "btor btormc" as the "btormc" tool was not found')
                elif self.config.presat:
                    self.log('disabling engine "btor pono" as it does not support presat checking')
                elif self.config.skip:
                    self.log('disabling engine "btor pono" as it does not support the "skip" option')
                else:
                    self.candidate("btor", "pono")

        for solver in ["yices", "z3"]:
            if not self.available(solver):
                self.log(f'disabling engine "smtbmc {solver}" as the solver "{solver}" was not found')
                continue
            for unroll in ["--unroll", "--nounroll"]:
                if solver == "yices" and self.config.forall:
                    self.log('disabling engine "smtbmc yices" due to limited forall support')
                    # TODO yices implicitly uses --noincr for forall problems and
                    # requires --stbv which does not play well with memory, still test it?
                    continue

                stmode = "--stdt" if self.config.forall else None

                for noincr in noincr_flags:
                    for presat in presat_flags:
                        self.candidate("smtbmc", presat, stmode, unroll, solver, noincr)

        if self.config.mode not in ["bmc", "prove"]:
            pass
        elif self.config.presat:
            self.log('disabling engines "abc" and "aiger" as they do not support presat checking')
        elif self.config.forall:
            self.log('disabling engines "abc" and "aiger" as they do not support forall')
        elif self.config.mem:
            self.log('disabling engines "abc" and "aiger" as they do not support memory')
        elif self.config.skip:
            self.log('disabling engines "abc" and "aiger" as they do not support the "skip" option')
        elif self.config.mode == "bmc":
            self.candidate("abc", "bmc3")

            if not self.available("aigbmc"):
                self.log('disabling engine "aiger aigbmc" as the "aigbmc" tool was not found')
            else:
                self.candidate("aiger", "aigbmc")
            # abc sim3 will never finish
        elif self.config.mode == "prove":
            self.candidate("abc", "pdr")

            if not self.available("suprove"):
                self.log('disabling engine "aiger suprove" as the "suprove" tool was not found')
            else:
                self.candidate("aiger", "suprove")
            # avy seems to crash in the presence of assumptions

    def log(self, message):
        self.task.log(message)

    def run(self):
        self.task.handle_non_engine_options()
        self.config = self.task.autotune_config or SbyAutotuneConfig()

        if "expect" not in self.task.options:
            self.task.expect = ["PASS", "FAIL"]
            # TODO check that solvers produce consistent results?

        if "TIMEOUT" in self.task.expect:
            self.task.error("cannot autotune a task with option 'expect timeout'")

        if self.task.reusedir:
            rmtree(f"{self.task.workdir}/model", ignore_errors=True)
        else:
            self.task.copy_src()

        self.model(None, "prep")
        self.task.taskloop.run()

        if self.task.status == "ERROR":
            return

        self.configure()

        self.build_candidates()
        if not self.active_candidates:
            self.error("no supported engines found for the current configuration and design")
        self.log(f"testing {len(self.active_candidates)} engine configurations...")

        self.start_engines()
        self.task.taskloop.run()

        self.finished_candidates.sort(key=lambda candidate: candidate.total_adjusted_time)

        if self.failed_candidates:
            self.log("failed engines:")
            for candidate in self.failed_candidates:
                self.log(
                    f"  engine_{candidate.engine_idx}: {' '.join(candidate.engine)}"
                    f" (returncode={candidate.engine_retcode} status={candidate.engine_status})"
                )

        if self.finished_candidates:
            self.log("finished engines:")
            for place, candidate in list(enumerate(self.finished_candidates, 1))[::-1]:
                self.log(
                    f"  #{place}: engine_{candidate.engine_idx}: {' '.join(candidate.engine)}"
                    f" ({candidate.total_adjusted_time} seconds, status={candidate.engine_status})"
                )

        if self.finished_candidates:
            self.task.status = "AUTOTUNED"
            self.task.retcode = 0
        elif self.failed_candidates:
            self.task.status = "FAIL"
            self.task.retcode = 2

        self.task_exit_callback()

    def next_candidate(self, peek=False):
        # peek=True is used to check whether we need to timeout running candidates to
        # give other candidates a chance.
        can_retry = None

        for candidate in self.active_candidates:
            if candidate.state == "pending":
                if not candidate.suspended:
                    return candidate
                if can_retry is None or can_retry.suspended > candidate.suspended:
                    can_retry = candidate

        if can_retry and not peek:
            shift = can_retry.suspended
            for candidate in self.active_candidates:
                if candidate.state == "pending":
                    candidate.suspended -= shift

        return can_retry

    def start_engines(self):
        self.task.taskloop.poll_now = True

        while self.threads_running < self.config.parallel:
            candidate = self.next_candidate()
            if candidate is None:
                self.have_pending_candidates = False
                return

            candidate_threads = candidate.threads()
            if self.threads_running:
                if self.threads_running + candidate_threads > self.config.parallel:
                    break

            candidate.set_running()
            candidate.set_engine_idx(self.next_engine_idx)
            self.next_engine_idx += 1

            try:
                engine_task = SbyAutotuneTask(self, candidate)
                pending = sum(c.state == "pending" for c in  self.active_candidates)
                self.log(f"{candidate.info} starting... ({pending} configurations pending)")
                self.threads_running += candidate_threads
                engine_task.setup_procs(False)
            except SbyAbort:
                pass

        self.have_pending_candidates = bool(self.next_candidate(peek=True))

    def engine_finished(self, engine_task):
        self.threads_running -= engine_task.candidate.threads()

        candidate = engine_task.candidate

        time = candidate.total_adjusted_time

        if engine_task.status == "TIMEOUT":
            if self.timeout is None or time < self.timeout:
                candidate.retry_later()
                self.log(f"{candidate.info} timeout ({time} seconds, will be retried if necessary)")
            else:
                candidate.timed_out()
                self.log(f"{candidate.info} timeout ({time} seconds)")
        elif engine_task.retcode:
            candidate.failed()
            self.log(f"{candidate.info} failed (returncode={candidate.engine_retcode} status={candidate.engine_status})")
        else:
            candidate.finished()

            self.log(f"{candidate.info} succeeded (status={candidate.engine_status})")

            if self.best_time is None:
                self.log(f"{candidate.info} took {time} seconds (first engine to finish)")
                self.best_time = time
            elif time < self.best_time:
                self.log(f"{candidate.info} took {time} seconds (best candidate, previous best: {self.best_time} seconds)")
                self.best_time = time
            else:
                self.log(f"{candidate.info} took {time} seconds")

            new_timeout = int(time + self.config.wait_seconds + time * self.config.wait_percentage // 100)

            if self.timeout is None or new_timeout < self.timeout:
                self.timeout = new_timeout

        self.start_engines()

    def model(self, engine_task, name):
        if self.task not in self.task.taskloop.tasks:
            self.task.taskloop.tasks.append(self.task)
        if name in self.model_requests:
            request = self.model_requests[name]
        else:
            self.model_requests[name] = request = SbyModelRequest(self, name)

        request.attach_engine_task(engine_task)

        return request.procs

    def proc_failed(self, proc):
        for name, request in self.model_requests.items():
            if proc in request.procs:
                for task in request.engine_tasks:
                    task = task or self.task
                    task.status = "ERROR"
                    task.log(f"could not prepare model '{name}', see toplevel logfile")
                    task.terminate()
        pass


class SbyModelRequest:
    """Handles sharing and canceling of model generation from several SbyAutotuneTask
    instances.
    """
    def __init__(self, autotune, name):
        self.autotune = autotune
        self.name = name
        self.engine_tasks = []

        autotune.log(f"model '{name}': preparing now...")

        self.make_model()

    def make_model(self):
        self.start_time = monotonic()
        self.total_time = None
        self.min_time = 0

        self.procs = self.autotune.task.model(self.name)
        for proc in self.procs:
            proc.register_dep(self)

    def attach_engine_task(self, engine_task):
        if self.total_time is None:
            if engine_task:
                if self.start_time is None:
                    model_time = 0
                    extra_time = self.min_time
                else:
                    model_time = monotonic() - self.start_time
                    extra_time = max(0, self.min_time - model_time)

                engine_task.model_time += model_time

                engine_task.check_timeout(extra_time)

            if self.start_time is None:
                self.make_model()

            self.engine_tasks.append(engine_task)
            if engine_task:
                engine_task.model_requests.append(self)

        else:
            if engine_task:
                engine_task.model_time += self.total_time

    def detach_engine_task(self, engine_task):
        self.engine_tasks.remove(engine_task)
        if not self.engine_tasks and self.total_time is None:
            self.autotune.log(f"cancelled model '{self.name}'")
            del self.autotune.task.models[self.name]
            for proc in self.procs:
                proc.terminate(True)

            self.min_time = max(self.min_time, monotonic() - self.start_time)
            self.start_time = None

            self.procs = []

    def poll(self):
        if self.total_time is None and all(proc.finished for proc in self.procs):
            self.autotune.log(f"prepared model '{self.name}'")

            self.total_time = self.min_time = monotonic() - self.start_time


class SbyAutotuneTask(SbyTask):
    """Task that shares the workdir with a parent task, runs in parallel to other
    autotune tasks and can be cancelled independent from other autotune tasks while
    sharing model generation with other tasks.
    """
    def __init__(self, autotune, candidate):
        task = autotune.task
        self.autotune = autotune
        self.candidate = candidate
        super().__init__(
            sbyconfig=None,
            workdir=task.workdir,
            early_logs=[],
            reusedir=True,
            taskloop=task.taskloop,
            logfile=open(f"{task.workdir}/engine_{candidate.engine_idx}_autotune.txt", "a"),
        )
        self.task_local_abort = True
        self.log_targets = [self.logfile]
        self.exe_paths = autotune.task.exe_paths
        self.reusedir = False
        self.design = autotune.task.design

        self.model_time = 0
        self.model_requests = []

        self.exit_callback = self.autotune_exit_callback


    def parse_config(self, f):
        super().parse_config(f)
        self.engines = []

    def engine_list(self):
        return [(self.candidate.engine_idx, self.candidate.engine)]

    def copy_src(self):
        pass

    def model(self, model_name):
        self.log(f"using model '{model_name}'")
        return self.autotune.model(self, model_name)

    def autotune_exit_callback(self):
        self.summarize()

        self.candidate.total_adjusted_time = int(monotonic() - self.start_clock_time + self.model_time)
        self.candidate.engine_retcode = self.retcode
        self.candidate.engine_status = self.status

        self.autotune.engine_finished(self)
        for request in self.model_requests:
            request.detach_engine_task(self)

    def check_timeout(self, extra_time=0):
        model_time = self.model_time + extra_time
        total_adjusted_time = int(monotonic() - self.start_clock_time + model_time)

        if self.autotune.timeout is not None:
            timeout = self.autotune.timeout
        else:
            if not self.autotune.have_pending_candidates:
                return
            timeout = self.candidate.soft_timeout

        if not self.timeout_reached and total_adjusted_time >= timeout:
            self.log(f"Reached autotune TIMEOUT ({timeout} seconds). Terminating all subprocesses.")
            self.status = "TIMEOUT"
            self.total_adjusted_time = total_adjusted_time
            self.terminate(timeout=True)
