#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2016  Claire Xenia Wolf <claire@yosyshq.com>
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

import os, re, sys, signal, platform, click
if os.name == "posix":
    import resource, fcntl
import subprocess
from dataclasses import dataclass, field
from collections import defaultdict
from typing import Optional
from shutil import copyfile, copytree, rmtree
from select import select
from time import monotonic, localtime, sleep, strftime
from sby_design import SbyProperty, SbyModule, design_hierarchy

all_procs_running = []

def force_shutdown(signum, frame):
    click.echo("SBY ---- Keyboard interrupt or external termination signal ----")
    for proc in list(all_procs_running):
        proc.terminate()
    sys.exit(1)

if os.name == "posix":
    signal.signal(signal.SIGHUP, force_shutdown)
signal.signal(signal.SIGINT, force_shutdown)
signal.signal(signal.SIGTERM, force_shutdown)

def process_filename(filename):
    if filename.startswith("~/"):
        filename = os.environ['HOME'] + filename[1:]

    filename = os.path.expandvars(filename)

    return filename

def dress_message(workdir, logmessage):
    tm = localtime()
    if workdir is not None:
        logmessage = "[" + click.style(workdir, fg="blue") + "] " + logmessage
    return " ".join([
        click.style("SBY", fg="blue"),
        click.style("{:2d}:{:02d}:{:02d}".format(tm.tm_hour, tm.tm_min, tm.tm_sec), fg="green"),
        logmessage
    ])

class SbyProc:
    def __init__(self, task, info, deps, cmdline, logfile=None, logstderr=True, silent=False):
        self.running = False
        self.finished = False
        self.terminated = False
        self.exited = False
        self.checkretcode = False
        self.retcodes = [0]
        self.task = task
        self.info = info
        self.deps = deps
        if os.name == "posix":
            self.cmdline = cmdline
        else:
            # Windows command interpreter equivalents for sequential
            # commands (; => &) command grouping ({} => ()).
            replacements = {
                ";" : "&",
                "{" : "(",
                "}" : ")",
            }
            parts = cmdline.split("'")
            for i in range(len(parts)):
                if i % 2 == 0:
                    cmdline_copy = parts[i]
                    for u, w in replacements.items():
                        cmdline_copy = cmdline_copy.replace(u, w)
                    parts[i] = cmdline_copy
            self.cmdline = '"'.join(parts)
        self.logfile = logfile
        self.noprintregex = None
        self.notify = []
        self.linebuffer = ""
        self.logstderr = logstderr
        self.silent = silent
        self.wait = False
        self.job_lease = None

        self.task.update_proc_pending(self)

        for dep in self.deps:
            dep.register_dep(self)

        self.output_callback = None
        self.exit_callbacks = []
        self.error_callback = None

        if self.task.timeout_reached:
            self.terminate(True)

    def register_dep(self, next_proc):
        if self.finished:
            next_proc.poll()
        else:
            self.notify.append(next_proc)

    def register_exit_callback(self, callback):
        self.exit_callbacks.append(callback)

    def log(self, line):
        if line is not None and (self.noprintregex is None or not self.noprintregex.match(line)):
            if self.logfile is not None:
                click.echo(line, file=self.logfile)
            self.task.log(f"{click.style(self.info, fg='magenta')}: {line}")

    def handle_output(self, line):
        if self.terminated or len(line) == 0:
            return
        if self.output_callback is not None:
            line = self.output_callback(line)
        self.log(line)

    def handle_exit(self, retcode):
        if self.terminated:
            return
        if self.logfile is not None:
            self.logfile.close()
        for callback in self.exit_callbacks:
            callback(retcode)

    def handle_error(self, retcode):
        if self.terminated:
            return
        if self.logfile is not None:
            self.logfile.close()
        if self.error_callback is not None:
            self.error_callback(retcode)

    def terminate(self, timeout=False):
        if (self.task.opt_wait or self.wait) and not timeout:
            return
        if self.running:
            if not self.silent:
                self.task.log(f"{click.style(self.info, fg='magenta')}: terminating process")
            if os.name == "posix":
                try:
                    os.killpg(self.p.pid, signal.SIGTERM)
                except PermissionError:
                    pass
            self.p.terminate()
            self.task.update_proc_stopped(self)
        elif not self.finished and not self.terminated and not self.exited:
            self.task.update_proc_canceled(self)
        self.terminated = True

    def poll(self, force_unchecked=False):
        if self.task.task_local_abort and not force_unchecked:
            try:
                self.poll(True)
            except SbyAbort:
                self.task.terminate(True)
            return
        if self.finished or self.terminated or self.exited:
            return

        if not self.running:
            for dep in self.deps:
                if not dep.finished:
                    return

            if self.task.taskloop.jobclient:
                if self.job_lease is None:
                    self.job_lease = self.task.taskloop.jobclient.request_lease()

                if not self.job_lease.is_ready:
                    return

            if not self.silent:
                self.task.log(f"{click.style(self.info, fg='magenta')}: starting process \"{self.cmdline}\"")

            if os.name == "posix":
                def preexec_fn():
                    signal.signal(signal.SIGINT, signal.SIG_IGN)
                    os.setpgrp()

                self.p = subprocess.Popen(["/usr/bin/env", "bash", "-c", self.cmdline], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                        stderr=(subprocess.STDOUT if self.logstderr else None), preexec_fn=preexec_fn)

                fl = fcntl.fcntl(self.p.stdout, fcntl.F_GETFL)
                fcntl.fcntl(self.p.stdout, fcntl.F_SETFL, fl | os.O_NONBLOCK)

            else:
                self.p = subprocess.Popen(self.cmdline + " & exit !errorlevel!", shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                        stderr=(subprocess.STDOUT if self.logstderr else None))

            self.task.update_proc_running(self)
            self.running = True
            return

        self.read_output()

        if self.p.poll() is not None:
            # The process might have written something since the last time we checked
            self.read_output()

            if self.job_lease:
                self.job_lease.done()

            if not self.silent:
                self.task.log(f"{click.style(self.info, fg='magenta')}: finished (returncode={self.p.returncode})")

            self.task.update_proc_stopped(self)
            self.running = False
            self.exited = True

            if os.name == "nt":
                if self.p.returncode == 9009:
                    returncode = 127
                else:
                    returncode = self.p.returncode & 0xff
            else:
                returncode = self.p.returncode

            if returncode == 127:
                if not self.silent:
                    self.task.log(f"{click.style(self.info, fg='magenta')}: COMMAND NOT FOUND. ERROR.")
                self.handle_error(returncode)
                self.terminated = True
                self.task.proc_failed(self)
                return

            if self.checkretcode and returncode not in self.retcodes:
                if not self.silent:
                    self.task.log(f"{click.style(self.info, fg='magenta')}: task failed. ERROR.")
                self.handle_error(returncode)
                self.terminated = True
                self.task.proc_failed(self)
                return

            self.handle_exit(returncode)

            self.finished = True
            for next_proc in self.notify:
                next_proc.poll()
            return

    def read_output(self):
        while True:
            outs = self.p.stdout.readline().decode("utf-8")
            if len(outs) == 0: break
            if outs[-1] != '\n':
                self.linebuffer += outs
                break
            outs = (self.linebuffer + outs).strip()
            self.linebuffer = ""
            self.handle_output(outs)


class SbyAbort(BaseException):
    pass


class SbyConfig:
    def __init__(self):
        self.options = dict()
        self.engines = dict()
        self.setup = dict()
        self.stage = dict()
        self.script = list()
        self.autotune_config = None
        self.files = dict()
        self.verbatim_files = dict()
        pass

    def parse_config(self, f):
        mode = None
        engine_mode = None
        stage_name = None

        for line in f:
            raw_line = line
            if mode in ["options", "engines", "files", "autotune", "setup", "stage"]:
                line = re.sub(r"\s*(\s#.*)?$", "", line)
                if line == "" or line[0] == "#":
                    continue
            else:
                line = line.rstrip()
            # print(line)
            if mode is None and (len(line) == 0 or line[0] == "#"):
                continue
            match = re.match(r"^\s*\[(.*)\]\s*$", line)
            if match:
                entries = match.group(1).strip().split(maxsplit = 1)
                if len(entries) == 0:
                    self.error(f"sby file syntax error: Expected section header, got '{line}'")
                elif len(entries) == 1:
                    section, args = (*entries, None)
                else:
                    section, args = entries

                if section == "options":
                    mode = "options"
                    if len(self.options) != 0:
                        self.error(f"sby file syntax error: '[options]' section already defined")

                    if args is not None:
                        self.error(f"sby file syntax error: '[options]' section does not accept any arguments. got {args}")
                    continue

                if section == "engines":
                    mode = "engines"

                    if args is None:
                        engine_mode = None
                    else:
                        section_args = args.split()

                        if len(section_args) > 1:
                            self.error(f"sby file syntax error: '[engines]' section expects at most 1 argument, got '{' '.join(section_args)}'")

                        if section_args[0] not in ("bmc", "prove", "cover", "live"):
                            self.error(f"sby file syntax error: Expected one of 'bmc', 'prove', 'cover', 'live' as '[engines]' argument, got '{section_args[0]}'")

                        engine_mode = section_args[0]

                    if engine_mode in self.engines:
                        if engine_mode is None:
                            self.error(f"Already defined engine block")
                        else:
                            self.error(f"Already defined engine block for mode '{engine_mode}'")
                    else:
                        self.engines[engine_mode] = list()

                    continue

                if section == "setup":
                    self.error(f"sby file syntax error: the '[setup]' section is not yet supported")

                    mode = "setup"
                    if len(self.setup) != 0:
                        self.error(f"sby file syntax error: '[setup]' section already defined")

                    if args is not None:
                        self.error(f"sby file syntax error: '[setup]' section does not accept any arguments, got '{args}'")

                    continue

                # [stage <NAME> (PARENTS,...)]
                if section == "stage":
                    self.error(f"sby file syntax error: the '[stage]' section is not yet supported")

                    mode = "stage"

                    if args is None:
                        self.error(f"sby file syntax error: '[stage]' section expects arguments, got none")

                    section_args = args.strip().split(maxsplit = 1)


                    if len(section_args) == 1:
                        parents = None
                    else:
                        parents = list(map(lambda a: a.strip(), section_args[1].split(',')))

                    stage_name = section_args[0]

                    if stage_name in self.stage:
                        self.error(f"stage '{stage_name}' already defined")

                    self.stage[stage_name] = {
                        'parents': parents
                    }

                    continue

                if section == "script":
                    mode = "script"
                    if len(self.script) != 0:
                        self.error(f"sby file syntax error: '[script]' section already defined")
                    if args is not None:
                        self.error(f"sby file syntax error: '[script]' section does not accept any arguments. got {args}")

                    continue

                if section == "autotune":
                    mode = "autotune"
                    if self.autotune_config:
                        self.error(f"sby file syntax error: '[autotune]' section already defined")

                    import sby_autotune
                    self.autotune_config = sby_autotune.SbyAutotuneConfig()
                    continue

                if section == "file":
                    mode = "file"
                    if args is None:
                        self.error(f"sby file syntax error: '[file]' section expects a file name argument")

                    section_args = args.split()

                    if len(section_args) > 1:
                        self.error(f"sby file syntax error: '[file]' section expects exactly one file name argument, got {len(section_args)}")
                    current_verbatim_file = section_args[0]
                    if current_verbatim_file in self.verbatim_files:
                        self.error(f"duplicate file: {current_verbatim_file}")
                    self.verbatim_files[current_verbatim_file] = list()
                    continue

                if section == "files":
                    mode = "files"
                    if args is not None:
                        self.error(f"sby file syntax error: '[files]' section does not accept any arguments. got {args}")
                    continue

                self.error(f"sby file syntax error: unexpected section '{section}', expected one of 'options, engines, script, autotune, file, files'")

            if mode == "options":
                entries = line.strip().split(maxsplit = 1)
                if len(entries) != 2:
                    self.error(f"sby file syntax error: '[options]' section entry does not have an argument '{line}'")
                self.options[entries[0]] = entries[1]
                continue

            if mode == "autotune":
                self.autotune_config.config_line(self, line)
                continue

            if mode == "engines":
                args = line.strip().split()
                self.engines[engine_mode].append(args)
                continue

            if mode == "setup":
                _valid_options = (
                    "cutpoint", "disable", "enable", "assume", "define"
                )

                args = line.strip().split(maxsplit = 1)

                if len(args) < 2:
                    self.error(f"sby file syntax error: entry in '[setup]' must have an argument, got '{' '.join(args)}'")

                if args[0] not in _valid_options:
                    self.error(f"sby file syntax error: expected one of '{', '.join(_valid_options)}' in '[setup]' section, got '{args[0]}'")

                else:
                    opt_key = args[0]
                    opt_args = args[1].strip().split()

                    if opt_key == 'define':
                        if 'define' not in self.setup:
                            self.setup['define'] = {}

                        if len(opt_args) != 2:
                            self.error(f"sby file syntax error: 'define' statement in '[setup]' section takes  exactly 2 arguments, got '{' '.join(opt_args)}'")

                        if opt_args[0][0] != '@':
                            self.error(f"sby file syntax error: 'define' statement in '[setup]' section expects an '@' prefixed name as the first parameter, got '{opt_args[0]}'")

                        name = opt_args[0][1:]
                        self.setup['define'][name] =  opt_args[2:]
                    else:
                        self.setup[opt_key] =  opt_args[1:]
                continue

            if mode == "stage":
                _valid_options = (
                    "mode", "depth", "timeout", "expect", "engine",
                    "cutpoint", "enable", "disable", "assume", "skip",
                    "check", "prove", "abstract", "setsel"
                )

                args = line.strip().split(maxsplit = 1)

                if args is None:
                    self.error(f"sby file syntax error: unknown key in '[stage]' section")

                if len(args) < 2:
                    self.error(f"sby file syntax error: entry in '[stage]' must have an argument, got {' '.join(args)}")

                if args[0] not in _valid_options:
                    self.error(f"sby file syntax error: expected one of '{', '.join(map(repr, _valid_options))}' in '[stage]' section, got '{args[0]}'")
                else:
                    opt_key = args[0]
                    opt_args = args[1].strip().split()
                    if opt_key == 'setsel':

                        if len(opt_args) != 2:
                            self.error(f"sby file syntax error: 'setsel' statement in '[stage]' section takes  exactly 2 arguments, got '{' '.join(opt_args)}'")

                        if opt_args[0][0] != '@':
                            self.error(f"sby file syntax error: 'setsel' statement in '[stage]' section expects an '@' prefixed name as the first parameter, got '{opt_args[0]}'")

                        name = opt_args[0][1:]

                        if stage_name not in self.stage:
                            self.stage[stage_name] = dict()

                        self.stage[stage_name][opt_key] = {
                            'name': name, 'pattern': opt_args[2:]
                        }

                    else:
                        if stage_name not in self.stage:
                            self.stage[stage_name] = dict()

                        self.stage[stage_name][opt_key] = opt_args[1:]
                continue

            if mode == "script":
                self.script.append(line)
                continue

            if mode == "files":
                entries = line.split()
                if len(entries) < 1 or len(entries) > 2:
                    self.error(f"sby file syntax error: '[files]' section entry expects up to 2 arguments, {len(entries)} specified")

                if len(entries) == 1:
                    self.files[os.path.basename(entries[0])] = entries[0]
                elif len(entries) == 2:
                    self.files[entries[0]] = entries[1]

                continue

            if mode == "file":
                self.verbatim_files[current_verbatim_file].append(raw_line)
                continue

            self.error(f"sby file syntax error: In an incomprehensible mode '{mode}'")

        if len(self.stage.keys()) == 0:
            self.stage['default'] = { 'enable': '*' }

    def error(self, logmessage):
        raise SbyAbort(logmessage)


class SbyTaskloop:
    def __init__(self, jobclient=None):
        self.procs_pending = []
        self.procs_running = []
        self.tasks = []
        self.poll_now = False
        self.jobclient = jobclient

    def run(self):
        for proc in self.procs_pending:
            proc.poll()


        waiting_for_jobslots = False
        if self.jobclient:
            waiting_for_jobslots = self.jobclient.has_pending_leases()

        while self.procs_running or waiting_for_jobslots or self.poll_now:
            fds = []
            if self.jobclient:
                fds.extend(self.jobclient.poll_fds())
            for proc in self.procs_running:
                if proc.running:
                    fds.append(proc.p.stdout)

            if not self.poll_now:
                if os.name == "posix":
                    try:
                        select(fds, [], [], 1.0) == ([], [], [])
                    except InterruptedError:
                        pass
                else:
                    sleep(0.1)
            self.poll_now = False

            if self.jobclient:
                self.jobclient.poll()

            self.procs_waiting = []

            for proc in self.procs_running:
                proc.poll()

            for proc in self.procs_pending:
                proc.poll()

            if self.jobclient:
                waiting_for_jobslots = self.jobclient.has_pending_leases()

            tasks = self.tasks
            self.tasks = []
            for task in tasks:
                task.check_timeout()
                if task.procs_pending or task.procs_running:
                    self.tasks.append(task)
                else:
                    task.exit_callback()

        for task in self.tasks:
            task.exit_callback()

@dataclass
class SbySummaryEvent:
    engine_idx: int
    trace: Optional[str] = field(default=None)
    path: Optional[str] = field(default=None)
    hdlname: Optional[str] = field(default=None)
    type: Optional[str] = field(default=None)
    src: Optional[str] = field(default=None)
    step: Optional[int] = field(default=None)
    prop: Optional[SbyProperty] = field(default=None)
    engine_case: Optional[str] = field(default=None)

    @property
    def engine(self):
        return f"engine_{self.engine_idx}"

@dataclass
class SbyTraceSummary:
    trace: str
    path: Optional[str] = field(default=None)
    engine_case: Optional[str] = field(default=None)
    events: dict = field(default_factory=lambda: defaultdict(lambda: defaultdict(list)))

    @property
    def kind(self):
        if '$assert' in self.events:
            kind = 'counterexample trace'
        elif '$cover' in self.events:
            kind = 'cover trace'
        else:
            kind = 'trace'
        return kind

@dataclass
class SbyEngineSummary:
    engine_idx: int
    traces: dict = field(default_factory=dict)
    status: Optional[str] = field(default=None)
    unreached_covers: Optional[list] = field(default=None)

    @property
    def engine(self):
        return f"engine_{self.engine_idx}"

class SbySummary:
    def __init__(self, task):
        self.task = task
        self.timing = []
        self.lines = []

        self.engine_summaries = {}
        self.traces = defaultdict(dict)
        self.engine_status = {}
        self.unreached_covers = None

    def append(self, line):
        self.lines.append(line)

    def extend(self, lines):
        self.lines.extend(lines)

    def engine_summary(self, engine_idx):
        if engine_idx not in self.engine_summaries:
            self.engine_summaries[engine_idx] = SbyEngineSummary(engine_idx)
        return self.engine_summaries[engine_idx]

    def add_event(self, *args, **kwargs):
        event = SbySummaryEvent(*args, **kwargs)
        if event.prop:
            if event.type == "$assert":
                event.prop.status = "FAIL"
                if event.path:
                    event.prop.tracefiles.append(event.path)
        if event.prop:
            if event.type == "$cover":
                event.prop.status = "PASS"
                if event.path:
                    event.prop.tracefiles.append(event.path)

        engine = self.engine_summary(event.engine_idx)

        if event.trace not in engine.traces:
            engine.traces[event.trace] = SbyTraceSummary(event.trace, path=event.path, engine_case=event.engine_case)

        if event.type:
            by_type = engine.traces[event.trace].events[event.type]
            if event.hdlname:
                by_type[event.hdlname].append(event)

    def set_engine_status(self, engine_idx, status, case=None):
        engine_summary = self.engine_summary(engine_idx)
        if case is None:
            self.task.log(f"{click.style(f'engine_{engine_idx}', fg='magenta')}: Status returned by engine: {status}")
            self.engine_summary(engine_idx).status = status
        else:
            self.task.log(f"{click.style(f'engine_{engine_idx}.{case}', fg='magenta')}: Status returned by engine for {case}: {status}")
            if engine_summary.status is None:
                engine_summary.status = {}
            engine_summary.status[case] = status

    def summarize(self, short):
        omitted_excess = False
        for line in self.timing:
            yield line

        for engine_idx, engine_cmd in self.task.engine_list():
            engine_cmd = ' '.join(engine_cmd)
            trace_limit = 5
            prop_limit = 5
            step_limit = 5
            engine = self.engine_summary(engine_idx)
            if isinstance(engine.status, dict):
                for case, status in sorted(engine.status.items()):
                    yield f"{engine.engine} ({engine_cmd}) returned {status} for {case}"
            elif engine.status:
                yield f"{engine.engine} ({engine_cmd}) returned {engine.status}"
            else:
                yield f"{engine.engine} ({engine_cmd}) did not return a status"

            produced_traces = False

            for i, (trace_name, trace) in enumerate(sorted(engine.traces.items())):
                if short and i == trace_limit:
                    excess = len(engine.traces) - trace_limit
                    omitted_excess = True
                    yield f"and {excess} further trace{'s' if excess != 1 else ''}"
                    break
                case_suffix = f" [{trace.engine_case}]" if trace.engine_case else ""
                if trace.path:
                    if short:
                        yield f"{trace.kind}{case_suffix}: {self.task.workdir}/{trace.path}"
                    else:
                        yield f"{trace.kind}{case_suffix}: {trace.path}"
                else:
                    yield f"{trace.kind}{case_suffix}: <{trace.trace}>"
                produced_traces = True
                for event_type, events in sorted(trace.events.items()):
                    if event_type == '$assert':
                        desc = "failed assertion"
                        short_desc = 'assertion'
                    elif event_type == '$cover':
                        desc = "reached cover statement"
                        short_desc = 'cover statement'
                    elif event_type == '$assume':
                        desc = "violated assumption"
                        short_desc = 'assumption'
                    else:
                        continue
                    for j, (hdlname, same_events) in enumerate(sorted(events.items())):
                        if short and j == prop_limit:
                            excess = len(events) - prop_limit
                            yield f"  and {excess} further {short_desc}{'s' if excess != 1 else ''}"
                            break

                        event = same_events[0]
                        steps = sorted(e.step for e in same_events)
                        if short and len(steps) > step_limit:
                            steps = [str(step) for step in steps[:step_limit]]
                            excess = len(steps) - step_limit
                            omitted_excess = True
                            steps[-1] += f" and {excess} further step{'s' if excess != 1 else ''}"

                        steps = f"step{'s' if len(steps) > 1 else ''} {', '.join(map(str, steps))}"
                        yield f"  {desc} {event.hdlname} at {event.src} in {steps}"

            if not produced_traces:
                yield f"{engine.engine} did not produce any traces"

        if self.unreached_covers is None and self.task.opt_mode == 'cover' and self.task.status != "PASS" and self.task.design:
            self.unreached_covers = []
            for prop in self.task.design.hierarchy:
                if prop.type == prop.Type.COVER and prop.status == "UNKNOWN":
                    self.unreached_covers.append(prop)

        if self.unreached_covers:
            yield f"unreached cover statements:"
            for j, prop in enumerate(self.unreached_covers):
                if short and j == prop_limit:
                    excess = len(self.unreached_covers) - prop_limit
                    omitted_excess = True
                    yield f"  and {excess} further propert{'ies' if excess != 1 else 'y'}"
                    break
                yield f"  {prop.hdlname} at {prop.location}"

        for line in self.lines:
            yield line

        if omitted_excess:
            yield f"see {self.task.workdir}/{self.task.status} for a complete summary"
    def __iter__(self):
        yield from self.summarize(True)



class SbyTask(SbyConfig):
    def __init__(self, sbyconfig, workdir, early_logs, reusedir, taskloop=None, logfile=None):
        super().__init__()
        self.used_options = set()
        self.models = dict()
        self.workdir = workdir
        self.reusedir = reusedir
        self.status = "UNKNOWN"
        self.total_time = 0
        self.expect = list()
        self.design = None
        self.precise_prop_status = False
        self.timeout_reached = False
        self.task_local_abort = False
        self.exit_callback = self.summarize

        yosys_program_prefix = "" ##yosys-program-prefix##
        self.exe_paths = {
            "yosys": os.getenv("YOSYS", yosys_program_prefix + "yosys"),
            "abc": os.getenv("ABC", yosys_program_prefix + "yosys-abc"),
            "smtbmc": os.getenv("SMTBMC", yosys_program_prefix + "yosys-smtbmc"),
            "witness": os.getenv("WITNESS", yosys_program_prefix + "yosys-witness"),
            "suprove": os.getenv("SUPROVE", "suprove"),
            "aigbmc": os.getenv("AIGBMC", "aigbmc"),
            "avy": os.getenv("AVY", "avy"),
            "btormc": os.getenv("BTORMC", "btormc"),
            "pono": os.getenv("PONO", "pono"),
        }

        self.taskloop = taskloop or SbyTaskloop()
        self.taskloop.tasks.append(self)

        self.procs_running = []
        self.procs_pending = []

        self.start_clock_time = monotonic()

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            self.start_process_time = ru.ru_utime + ru.ru_stime

        self.summary = SbySummary(self)

        self.logfile = logfile or open(f"{workdir}/logfile.txt", "a")
        self.log_targets = [sys.stdout, self.logfile]

        for line in early_logs:
            click.echo(line, file=self.logfile)

        if not reusedir:
            with open(f"{workdir}/config.sby", "w") as f:
                for line in sbyconfig:
                    click.echo(line, file=f)

    def engine_list(self):
        engines = self.engines.get(None, []) + self.engines.get(self.opt_mode, [])
        return list(enumerate(engines))

    def check_timeout(self):
        if self.opt_timeout is not None:
            total_clock_time = int(monotonic() - self.start_clock_time)
            if total_clock_time > self.opt_timeout:
                self.log(f"Reached TIMEOUT ({self.opt_timeout} seconds). Terminating all subprocesses.")
                self.status = "TIMEOUT"
                self.terminate(timeout=True)

    def update_proc_pending(self, proc):
        self.procs_pending.append(proc)
        self.taskloop.procs_pending.append(proc)

    def update_proc_running(self, proc):
        self.procs_pending.remove(proc)
        self.taskloop.procs_pending.remove(proc)

        self.procs_running.append(proc)
        self.taskloop.procs_running.append(proc)
        all_procs_running.append(proc)

    def update_proc_stopped(self, proc):
        self.procs_running.remove(proc)
        self.taskloop.procs_running.remove(proc)
        all_procs_running.remove(proc)

    def update_proc_canceled(self, proc):
        self.procs_pending.remove(proc)
        self.taskloop.procs_pending.remove(proc)

    def log(self, logmessage):
        tm = localtime()
        line = dress_message(self.workdir, logmessage)
        for target in self.log_targets:
            click.echo(line, file=target)

    def log_prefix(self, prefix, message=None):
        prefix = f"{click.style(prefix, fg='magenta')}: "
        def log(message):
            self.log(f"{prefix}{message}")
        if message is None:
            return log
        else:
            log(message)

    def error(self, logmessage):
        tm = localtime()
        self.log(click.style(f"ERROR: {logmessage}", fg="red", bold=True))
        self.status = "ERROR"
        if "ERROR" not in self.expect:
            self.retcode = 16
        else:
            self.retcode = 0
        self.terminate()
        with open(f"{self.workdir}/{self.status}", "w") as f:
            click.echo(f"ERROR: {logmessage}", file=f)
        raise SbyAbort(logmessage)

    def makedirs(self, path):
        if self.reusedir and os.path.isdir(path):
            rmtree(path, ignore_errors=True)
        if not os.path.isdir(path):
            os.makedirs(path)

    def copy_src(self):
        self.makedirs(self.workdir + "/src")

        for dstfile, lines in self.verbatim_files.items():
            dstfile = self.workdir + "/src/" + dstfile
            self.log(f"Writing '{dstfile}'.")

            with open(dstfile, "w") as f:
                for line in lines:
                    f.write(line)

        for dstfile, srcfile in self.files.items():
            if dstfile.startswith("/") or dstfile.startswith("../") or ("/../" in dstfile):
                self.error(f"destination filename must be a relative path without /../: {dstfile}")
            dstfile = self.workdir + "/src/" + dstfile

            srcfile = process_filename(srcfile)

            basedir = os.path.dirname(dstfile)
            if basedir != "" and not os.path.exists(basedir):
                os.makedirs(basedir)

            self.log(f"Copy '{os.path.abspath(srcfile)}' to '{os.path.abspath(dstfile)}'.")
            if os.path.isdir(srcfile):
                copytree(srcfile, dstfile, dirs_exist_ok=True)
            else:
                copyfile(srcfile, dstfile)

    def handle_str_option(self, option_name, default_value):
        if option_name in self.options:
            self.__dict__["opt_" + option_name] = self.options[option_name]
            self.used_options.add(option_name)
        else:
            self.__dict__["opt_" + option_name] = default_value

    def handle_int_option(self, option_name, default_value):
        if option_name in self.options:
            self.__dict__["opt_" + option_name] = int(self.options[option_name])
            self.used_options.add(option_name)
        else:
            self.__dict__["opt_" + option_name] = default_value

    def handle_bool_option(self, option_name, default_value):
        if option_name in self.options:
            if self.options[option_name] not in ["on", "off"]:
                self.error(f"Invalid value '{self.options[option_name]}' for boolean option {option_name}.")
            self.__dict__["opt_" + option_name] = self.options[option_name] == "on"
            self.used_options.add(option_name)
        else:
            self.__dict__["opt_" + option_name] = default_value

    def make_model(self, model_name):
        if not os.path.isdir(f"{self.workdir}/model"):
            os.makedirs(f"{self.workdir}/model")

        if model_name == "prep":
            with open(f"""{self.workdir}/model/design_prep.ys""", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print(f"""read_ilang design.il""", file=f)
                print("scc -select; simplemap; select -clear", file=f)
                print("memory_nordff", file=f)
                if self.opt_multiclock:
                    print("clk2fflogic", file=f)
                else:
                    print("async2sync", file=f)
                    print("chformal -assume -early", file=f)
                print("opt_clean", file=f)
                print("formalff -setundef -clk2ff -ff2anyinit -hierarchy", file=f)
                if self.opt_mode in ["bmc", "prove"]:
                    print("chformal -live -fair -cover -remove", file=f)
                if self.opt_mode == "cover":
                    print("chformal -live -fair -remove", file=f)
                if self.opt_mode == "live":
                    print("chformal -assert2assume", file=f)
                    print("chformal -cover -remove", file=f)
                print("opt_clean", file=f)
                print("check", file=f)  # can't detect undriven wires past this point
                print("setundef -undriven -anyseq", file=f)
                print("opt -fast", file=f)
                if self.opt_witrename:
                    print("rename -witness", file=f)
                    print("opt_clean", file=f)
                print(f"""write_rtlil ../model/design_prep.il""", file=f)

            proc = SbyProc(
                self,
                model_name,
                self.model("base"),
                "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name)
            )
            proc.checkretcode = True

            return [proc]

        if model_name == "base":
            with open(f"""{self.workdir}/model/design.ys""", "w") as f:
                print(f"# running in {self.workdir}/src/", file=f)
                for cmd in self.script:
                    print(cmd, file=f)
                # the user must designate a top module in [script]
                print("hierarchy -smtcheck", file=f)
                print(f"""write_jny -no-connections ../model/design.json""", file=f)
                print(f"""write_rtlil ../model/design.il""", file=f)

            proc = SbyProc(
                self,
                model_name,
                [],
                "cd {}/src; {} -ql ../model/design.log ../model/design.ys".format(self.workdir, self.exe_paths["yosys"])
            )
            proc.checkretcode = True

            def instance_hierarchy_callback(retcode):
                if self.design == None:
                    with open(f"{self.workdir}/model/design.json") as f:
                        self.design = design_hierarchy(f)

            def instance_hierarchy_error_callback(retcode):
                self.precise_prop_status = False

            proc.register_exit_callback(instance_hierarchy_callback)
            proc.error_callback = instance_hierarchy_error_callback

            return [proc]

        if re.match(r"^smt2(_syn)?(_nomem)?(_stbv|_stdt)?$", model_name):
            with open(f"{self.workdir}/model/design_{model_name}.ys", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print(f"""read_ilang design_prep.il""", file=f)
                print("hierarchy -smtcheck", file=f)
                print("formalff -assume", file=f)
                if "_nomem" in model_name:
                    print("memory_map -formal", file=f)
                    print("formalff -setundef -clk2ff -ff2anyinit", file=f)
                if "_syn" in model_name:
                    print("techmap", file=f)
                    print("opt -fast", file=f)
                    print("abc", file=f)
                    print("opt_clean", file=f)
                print("dffunmap", file=f)
                print("stat", file=f)
                if "_stbv" in model_name:
                    print(f"write_smt2 -stbv -wires design_{model_name}.smt2", file=f)
                elif "_stdt" in model_name:
                    print(f"write_smt2 -stdt -wires design_{model_name}.smt2", file=f)
                else:
                    print(f"write_smt2 -wires design_{model_name}.smt2", file=f)

            proc = SbyProc(
                self,
                model_name,
                self.model("prep"),
                "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name)
            )
            proc.checkretcode = True

            return [proc]

        if re.match(r"^btor(_syn)?(_nomem)?$", model_name):
            with open(f"{self.workdir}/model/design_{model_name}.ys", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print(f"""read_ilang design_prep.il""", file=f)
                print("hierarchy -simcheck", file=f)
                print("formalff -assume", file=f)
                if "_nomem" in model_name:
                    print("memory_map -formal", file=f)
                    print("formalff -setundef -clk2ff -ff2anyinit", file=f)
                print("flatten", file=f)
                print("setundef -undriven -anyseq", file=f)
                if "_syn" in model_name:
                    print("opt -full", file=f)
                    print("techmap", file=f)
                    print("opt -fast", file=f)
                    print("abc", file=f)
                    print("opt_clean", file=f)
                else:
                    print("opt -fast", file=f)
                print("delete -output", file=f)
                print("dffunmap", file=f)
                print("stat", file=f)
                print("write_btor {}-i design_{m}.info -ywmap design_btor.ywb design_{m}.btor".format("-c " if self.opt_mode == "cover" else "", m=model_name), file=f)
                print("write_btor -s {}-i design_{m}_single.info -ywmap design_btor_single.ywb design_{m}_single.btor".format("-c " if self.opt_mode == "cover" else "", m=model_name), file=f)

            proc = SbyProc(
                self,
                model_name,
                self.model("prep"),
                "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name)
            )
            proc.checkretcode = True

            return [proc]

        if model_name == "aig":
            with open(f"{self.workdir}/model/design_aiger.ys", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print("read_ilang design_prep.il", file=f)
                print("hierarchy -simcheck", file=f)
                print("formalff -assume", file=f)
                print("flatten", file=f)
                print("setundef -undriven -anyseq", file=f)
                print("setattr -unset keep", file=f)
                print("delete -output", file=f)
                print("opt -full", file=f)
                print("techmap", file=f)
                print("opt -fast", file=f)
                print("memory_map -formal", file=f)
                print("formalff -clk2ff -ff2anyinit", file=f)
                print("simplemap", file=f)
                print("dffunmap", file=f)
                print("abc -g AND -fast", file=f)
                print("opt_clean", file=f)
                print("stat", file=f)
                print(f"write_aiger -I -B -zinit -no-startoffset {'-vmap' if self.opt_aigvmap else '-map'} design_aiger.aim" +
                        f"{' -symbols' if self.opt_aigsyms else ''} -ywmap design_aiger.ywa design_aiger.aig", file=f)

            proc = SbyProc(
                self,
                "aig",
                self.model("prep"),
                f"""cd {self.workdir}/model; {self.exe_paths["yosys"]} -ql design_aiger.log design_aiger.ys"""
            )
            proc.checkretcode = True

            return [proc]

        if model_name == "aig_fold":
            proc = SbyProc(
                self,
                model_name,
                self.model("aig"),
                f"""cd {self.workdir}/model; {self.exe_paths["abc"]} -c 'read_aiger design_aiger.aig; fold{" -s" if self.opt_aigfolds else ""}; strash; write_aiger design_aiger_fold.aig'""",
                logfile=open(f"{self.workdir}/model/design_aiger_fold.log", "w")
            )
            proc.checkretcode = True

            return [proc]

        self.error(f"Invalid model name: {model_name}")

    def model(self, model_name):
        if model_name not in self.models:
            self.models[model_name] = self.make_model(model_name)
        return self.models[model_name]

    def terminate(self, timeout=False):
        if timeout:
            self.timeout_reached = True
        for proc in list(self.procs_running):
            proc.terminate(timeout=timeout)
        for proc in list(self.procs_pending):
            proc.terminate(timeout=timeout)

    def proc_failed(self, proc):
        # proc parameter used by autotune override
        self.status = "ERROR"
        self.terminate()

    def update_status(self, new_status):
        assert new_status in ["PASS", "FAIL", "UNKNOWN", "ERROR"]

        if new_status == "UNKNOWN":
            return

        if self.status == "ERROR":
            return

        if new_status == "PASS":
            assert self.status != "FAIL"
            self.status = "PASS"
            if self.opt_mode in ("bmc", "prove") and self.design:
                self.design.pass_unknown_asserts()

        elif new_status == "FAIL":
            assert self.status != "PASS"
            self.status = "FAIL"

        elif new_status == "ERROR":
            self.status = "ERROR"

        else:
            assert 0

    def handle_non_engine_options(self):
        with open(f"{self.workdir}/config.sby", "r") as f:
            self.parse_config(f)

        self.handle_str_option("mode", None)

        if self.opt_mode not in ["bmc", "prove", "cover", "live"]:
            self.error(f"Invalid mode: {self.opt_mode}")

        self.expect = ["PASS"]
        if "expect" in self.options:
            self.expect = self.options["expect"].upper().split(",")
            self.used_options.add("expect")

        for s in self.expect:
            if s not in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]:
                self.error(f"Invalid expect value: {s}")

        if self.opt_mode != "live":
            self.handle_int_option("depth", 20)

        self.handle_bool_option("multiclock", False)
        self.handle_bool_option("wait", False)
        self.handle_int_option("timeout", None)

        self.handle_bool_option("vcd", True)
        self.handle_bool_option("vcd_sim", False)
        self.handle_bool_option("fst", False)

        self.handle_bool_option("witrename", True)
        self.handle_bool_option("aigfolds", False)
        self.handle_bool_option("aigvmap", False)
        self.handle_bool_option("aigsyms", False)

        self.handle_str_option("smtc", None)
        self.handle_int_option("skip", None)
        self.handle_str_option("tbtop", None)

        if self.opt_mode != "live":
            self.handle_int_option("append", 0)
            self.handle_bool_option("append_assume", True)

        self.handle_str_option("make_model", None)

    def setup_procs(self, setupmode):
        self.handle_non_engine_options()
        if self.opt_smtc is not None:
            for engine_idx, engine in self.engine_list():
                if engine[0] != "smtbmc":
                    self.error("Option smtc is only valid for smtbmc engine.")

        if self.opt_skip is not None:
            if self.opt_skip == 0:
                self.opt_skip = None
            else:
                for engine_idx, engine in self.engine_list():
                    if engine[0] not in ["smtbmc", "btor"]:
                        self.error("Option skip is only valid for smtbmc and btor engines.")

        if len(self.engine_list()) == 0:
            self.error("Config file is lacking engine configuration.")

        if self.reusedir:
            rmtree(f"{self.workdir}/model", ignore_errors=True)
        else:
            self.copy_src()

        if setupmode:
            self.retcode = 0
            return

        if self.opt_make_model is not None:
            for name in self.opt_make_model.split(","):
                self.model(name.strip())

            for proc in self.procs_pending:
                proc.wait = True

        if self.opt_mode == "bmc":
            import sby_mode_bmc
            sby_mode_bmc.run(self)

        elif self.opt_mode == "prove":
            import sby_mode_prove
            sby_mode_prove.run(self)

        elif self.opt_mode == "live":
            import sby_mode_live
            sby_mode_live.run(self)

        elif self.opt_mode == "cover":
            import sby_mode_cover
            sby_mode_cover.run(self)

        else:
            assert False

        for opt in self.options.keys():
            if opt not in self.used_options:
                self.error(f"Unused option: {opt}")

    def summarize(self):
        total_clock_time = int(monotonic() - self.start_clock_time)

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            total_process_time = int((ru.ru_utime + ru.ru_stime) - self.start_process_time)
            self.total_time = total_process_time

            # TODO process time is incorrect when running in parallel

            self.summary.timing = [
                "Elapsed clock time [H:MM:SS (secs)]: {}:{:02d}:{:02d} ({})".format
                        (total_clock_time // (60*60), (total_clock_time // 60) % 60, total_clock_time % 60, total_clock_time),
                "Elapsed process time [H:MM:SS (secs)]: {}:{:02d}:{:02d} ({})".format
                        (total_process_time // (60*60), (total_process_time // 60) % 60, total_process_time % 60, total_process_time),
            ]
        else:
            self.summary.timing = [
                "Elapsed clock time [H:MM:SS (secs)]: {}:{:02d}:{:02d} ({})".format
                        (total_clock_time // (60*60), (total_clock_time // 60) % 60, total_clock_time % 60, total_clock_time),
                "Elapsed process time unvailable on Windows"
            ]

        for line in self.summary:
            if line.startswith("Elapsed"):
                self.log(f"summary: {line}")
            else:
                self.log("summary: " + click.style(line, fg="green" if self.status in self.expect else "red", bold=True))

        assert self.status in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]

        if self.status in self.expect:
            self.retcode = 0
        else:
            if self.status == "PASS": self.retcode = 1
            if self.status == "FAIL": self.retcode = 2
            if self.status == "UNKNOWN": self.retcode = 4
            if self.status == "TIMEOUT": self.retcode = 8
            if self.status == "ERROR": self.retcode = 16

    def write_summary_file(self):
        with open(f"{self.workdir}/{self.status}", "w") as f:
            for line in self.summary.summarize(short=False):
                click.echo(line, file=f)

    def print_junit_result(self, f, junit_ts_name, junit_tc_name, junit_format_strict=False):
        junit_time = strftime('%Y-%m-%dT%H:%M:%S')
        if not self.design:
            self.precise_prop_status = False
        if self.precise_prop_status:
            checks = self.design.hierarchy.get_property_list()
            junit_tests = len(checks)
            junit_failures = 0
            junit_errors = 0
            junit_skipped = 0
            for check in checks:
                if check.status == "PASS":
                    pass
                elif check.status == "FAIL":
                    junit_failures += 1
                elif check.status == "UNKNOWN":
                    junit_skipped += 1
                else:
                    junit_errors += 1
            if self.retcode == 16:
                junit_errors += 1
            elif self.retcode != 0:
                junit_failures += 1
        else:
            junit_tests = 1
            junit_errors = 1 if self.retcode == 16 else 0
            junit_failures = 1 if self.retcode != 0 and junit_errors == 0 else 0
            junit_skipped = 0
        print(f'<?xml version="1.0" encoding="UTF-8"?>', file=f)
        print(f'<testsuites>', file=f)
        print(f'<testsuite timestamp="{junit_time}" hostname="{platform.node()}" package="{junit_ts_name}" id="0" name="{junit_tc_name}" tests="{junit_tests}" errors="{junit_errors}" failures="{junit_failures}" time="{self.total_time}" skipped="{junit_skipped}">', file=f)
        print(f'<properties>', file=f)
        print(f'<property name="os" value="{platform.system()}"/>', file=f)
        print(f'<property name="expect" value="{", ".join(self.expect)}"/>', file=f)
        print(f'<property name="status" value="{self.status}"/>', file=f)
        print(f'</properties>', file=f)
        if self.precise_prop_status:
            print(f'<testcase classname="{junit_tc_name}" name="build execution" time="0">', file=f)
            if self.retcode == 16:
                print(f'<error type="ERROR"/>', file=f) # type mandatory, message optional
            elif self.retcode != 0:
                if len(self.expect) > 1 or "PASS" not in self.expect:
                    expected = " ".join(self.expect)
                    print(f'<failure type="EXPECT" message="Task returned status {self.status}. Expected values were: {expected}" />', file=f)
                else:
                    print(f'<failure type="{self.status}" message="Task returned status {self.status}." />', file=f)
            print(f'</testcase>', file=f)

            for check in checks:
                if junit_format_strict:
                    detail_attrs = ''
                else:
                    detail_attrs = f' type="{check.type}" location="{check.location}" id="{check.name}"'
                    if check.tracefile:
                        detail_attrs += f' tracefile="{check.tracefile}"'
                if check.location:
                    junit_prop_name = f"Property {check.type} in {check.hierarchy} at {check.location}"
                else:
                    junit_prop_name = f"Property {check.type} {check.name} in {check.hierarchy}"
                print(f'<testcase classname="{junit_tc_name}" name="{junit_prop_name}" time="0"{detail_attrs}>', file=f)
                if check.status == "PASS":
                    pass
                elif check.status == "UNKNOWN":
                    print(f'<skipped />', file=f)
                elif check.status == "FAIL":
                    traceinfo = f' Trace file: {check.tracefile}' if check.type == check.Type.ASSERT else ''
                    print(f'<failure type="{check.type}" message="{junit_prop_name} failed.{traceinfo}" />', file=f)
                elif check.status == "ERROR":
                    print(f'<error type="ERROR"/>', file=f) # type mandatory, message optional
                print(f'</testcase>', file=f)
        else:
            print(f'<testcase classname="{junit_tc_name}" name="{junit_tc_name}" time="{self.total_time}">', file=f)
            if junit_errors:
                print(f'<error type="ERROR"/>', file=f) # type mandatory, message optional
            elif junit_failures:
                junit_type = "assert" if self.opt_mode in ["bmc", "prove"] else self.opt_mode
                print(f'<failure type="{junit_type}" message="{self.status}" />', file=f)
            print(f'</testcase>', file=f)
        print('<system-out>', end="", file=f)
        with open(f"{self.workdir}/logfile.txt", "r") as logf:
            for line in logf:
                print(line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;"), end="", file=f)
        print('</system-out>', file=f)
        print('<system-err>', file=f)
        #TODO: can we handle errors and still output this file?
        print('</system-err>', file=f)
        print(f'</testsuite>', file=f)
        print(f'</testsuites>', file=f)
