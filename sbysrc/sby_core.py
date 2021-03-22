#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2016  Clifford Wolf <clifford@clifford.at>
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

import os, re, sys, signal
if os.name == "posix":
    import resource, fcntl
import subprocess
from shutil import copyfile, rmtree
from select import select
from time import time, localtime, sleep

all_tasks_running = []

def force_shutdown(signum, frame):
    print("SBY ---- Keyboard interrupt or external termination signal ----", flush=True)
    for task in list(all_tasks_running):
        task.terminate()
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

class SbyTask:
    def __init__(self, job, info, deps, cmdline, logfile=None, logstderr=True, silent=False):
        self.running = False
        self.finished = False
        self.terminated = False
        self.checkretcode = False
        self.job = job
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

        self.job.tasks_pending.append(self)

        for dep in self.deps:
            dep.register_dep(self)

        self.output_callback = None
        self.exit_callback = None

    def register_dep(self, next_task):
        if self.finished:
            next_task.poll()
        else:
            self.notify.append(next_task)

    def log(self, line):
        if line is not None and (self.noprintregex is None or not self.noprintregex.match(line)):
            if self.logfile is not None:
                print(line, file=self.logfile)
            self.job.log("{}: {}".format(self.info, line))

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
        if self.exit_callback is not None:
            self.exit_callback(retcode)

    def terminate(self, timeout=False):
        if self.job.opt_wait and not timeout:
            return
        if self.running:
            if not self.silent:
                self.job.log("{}: terminating process".format(self.info))
            if os.name == "posix":
                try:
                    os.killpg(self.p.pid, signal.SIGTERM)
                except PermissionError:
                    pass
            self.p.terminate()
            self.job.tasks_running.remove(self)
            all_tasks_running.remove(self)
        self.terminated = True

    def poll(self):
        if self.finished or self.terminated:
            return

        if not self.running:
            for dep in self.deps:
                if not dep.finished:
                    return

            if not self.silent:
                self.job.log("{}: starting process \"{}\"".format(self.info, self.cmdline))

            if os.name == "posix":
                def preexec_fn():
                    signal.signal(signal.SIGINT, signal.SIG_IGN)
                    os.setpgrp()

                self.p = subprocess.Popen(["/usr/bin/env", "bash", "-c", self.cmdline], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                        stderr=(subprocess.STDOUT if self.logstderr else None), preexec_fn=preexec_fn)

                fl = fcntl.fcntl(self.p.stdout, fcntl.F_GETFL)
                fcntl.fcntl(self.p.stdout, fcntl.F_SETFL, fl | os.O_NONBLOCK)

            else:
                self.p = subprocess.Popen(self.cmdline, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                        stderr=(subprocess.STDOUT if self.logstderr else None))

            self.job.tasks_pending.remove(self)
            self.job.tasks_running.append(self)
            all_tasks_running.append(self)
            self.running = True
            return

        while True:
            outs = self.p.stdout.readline().decode("utf-8")
            if len(outs) == 0: break
            if outs[-1] != '\n':
                self.linebuffer += outs
                break
            outs = (self.linebuffer + outs).strip()
            self.linebuffer = ""
            self.handle_output(outs)

        if self.p.poll() is not None:
            if not self.silent:
                self.job.log("{}: finished (returncode={})".format(self.info, self.p.returncode))
            self.job.tasks_running.remove(self)
            all_tasks_running.remove(self)
            self.running = False

            if self.p.returncode == 127:
                self.job.status = "ERROR"
                if not self.silent:
                    self.job.log("{}: COMMAND NOT FOUND. ERROR.".format(self.info))
                self.terminated = True
                self.job.terminate()
                return

            self.handle_exit(self.p.returncode)

            if self.checkretcode and self.p.returncode != 0:
                self.job.status = "ERROR"
                if not self.silent:
                    self.job.log("{}: job failed. ERROR.".format(self.info))
                self.terminated = True
                self.job.terminate()
                return

            self.finished = True
            for next_task in self.notify:
                next_task.poll()
            return


class SbyAbort(BaseException):
    pass


class SbyJob:
    def __init__(self, sbyconfig, workdir, early_logs, reusedir):
        self.options = dict()
        self.used_options = set()
        self.engines = list()
        self.script = list()
        self.files = dict()
        self.verbatim_files = dict()
        self.models = dict()
        self.workdir = workdir
        self.reusedir = reusedir
        self.status = "UNKNOWN"
        self.total_time = 0
        self.expect = []

        yosys_program_prefix = "" ##yosys-program-prefix##
        self.exe_paths = {
            "yosys": os.getenv("YOSYS", yosys_program_prefix + "yosys"),
            "abc": os.getenv("ABC", yosys_program_prefix + "yosys-abc"),
            "smtbmc": os.getenv("SMTBMC", yosys_program_prefix + "yosys-smtbmc"),
            "suprove": os.getenv("SUPROVE", "suprove"),
            "aigbmc": os.getenv("AIGBMC", "aigbmc"),
            "avy": os.getenv("AVY", "avy"),
            "btormc": os.getenv("BTORMC", "btormc"),
            "pono": os.getenv("PONO", "pono"),
        }

        self.tasks_running = []
        self.tasks_pending = []

        self.start_clock_time = time()

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            self.start_process_time = ru.ru_utime + ru.ru_stime

        self.summary = list()

        self.logfile = open("{}/logfile.txt".format(workdir), "a")

        for line in early_logs:
            print(line, file=self.logfile, flush=True)

        if not reusedir:
            with open("{}/config.sby".format(workdir), "w") as f:
                for line in sbyconfig:
                    print(line, file=f)

    def taskloop(self):
        for task in self.tasks_pending:
            task.poll()

        while len(self.tasks_running):
            fds = []
            for task in self.tasks_running:
                if task.running:
                    fds.append(task.p.stdout)

            if os.name == "posix":
                try:
                    select(fds, [], [], 1.0) == ([], [], [])
                except InterruptedError:
                    pass
            else:
                sleep(0.1)

            for task in self.tasks_running:
                task.poll()

            for task in self.tasks_pending:
                task.poll()

            if self.opt_timeout is not None:
                total_clock_time = int(time() - self.start_clock_time)
                if total_clock_time > self.opt_timeout:
                    self.log("Reached TIMEOUT ({} seconds). Terminating all tasks.".format(self.opt_timeout))
                    self.status = "TIMEOUT"
                    self.terminate(timeout=True)

    def log(self, logmessage):
        tm = localtime()
        print("SBY {:2d}:{:02d}:{:02d} [{}] {}".format(tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage), flush=True)
        print("SBY {:2d}:{:02d}:{:02d} [{}] {}".format(tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage), file=self.logfile, flush=True)

    def error(self, logmessage):
        tm = localtime()
        print("SBY {:2d}:{:02d}:{:02d} [{}] ERROR: {}".format(tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage), flush=True)
        print("SBY {:2d}:{:02d}:{:02d} [{}] ERROR: {}".format(tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage), file=self.logfile, flush=True)
        self.status = "ERROR"
        if "ERROR" not in self.expect:
            self.retcode = 16
        self.terminate()
        with open("{}/{}".format(self.workdir, self.status), "w") as f:
            print("ERROR: {}".format(logmessage), file=f)
        raise SbyAbort(logmessage)

    def makedirs(self, path):
        if self.reusedir and os.path.isdir(path):
            rmtree(path, ignore_errors=True)
        os.makedirs(path)

    def copy_src(self):
        os.makedirs(self.workdir + "/src")

        for dstfile, lines in self.verbatim_files.items():
            dstfile = self.workdir + "/src/" + dstfile
            self.log("Writing '{}'.".format(dstfile))

            with open(dstfile, "w") as f:
                for line in lines:
                    f.write(line)

        for dstfile, srcfile in self.files.items():
            if dstfile.startswith("/") or dstfile.startswith("../") or ("/../" in dstfile):
                self.error("destination filename must be a relative path without /../: {}".format(dstfile))
            dstfile = self.workdir + "/src/" + dstfile

            srcfile = process_filename(srcfile)

            basedir = os.path.dirname(dstfile)
            if basedir != "" and not os.path.exists(basedir):
                os.makedirs(basedir)

            self.log("Copy '{}' to '{}'.".format(srcfile, dstfile))
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
                self.error("Invalid value '{}' for boolean option {}.".format(self.options[option_name], option_name))
            self.__dict__["opt_" + option_name] = self.options[option_name] == "on"
            self.used_options.add(option_name)
        else:
            self.__dict__["opt_" + option_name] = default_value

    def make_model(self, model_name):
        if not os.path.isdir("{}/model".format(self.workdir)):
            os.makedirs("{}/model".format(self.workdir))

        if model_name in ["base", "nomem"]:
            with open("{}/model/design{}.ys".format(self.workdir, "" if model_name == "base" else "_nomem"), "w") as f:
                print("# running in {}/src/".format(self.workdir), file=f)
                for cmd in self.script:
                    print(cmd, file=f)
                if model_name == "base":
                    print("memory_nordff", file=f)
                else:
                    print("memory_map", file=f)
                if self.opt_multiclock:
                    print("clk2fflogic", file=f)
                else:
                    print("async2sync", file=f)
                    print("chformal -assume -early", file=f)
                if self.opt_mode in ["bmc", "prove"]:
                    print("chformal -live -fair -cover -remove", file=f)
                if self.opt_mode == "cover":
                    print("chformal -live -fair -remove", file=f)
                if self.opt_mode == "live":
                    print("chformal -assert2assume", file=f)
                    print("chformal -cover -remove", file=f)
                print("opt_clean", file=f)
                print("setundef -anyseq", file=f)
                print("opt -keepdc -fast", file=f)
                print("check", file=f)
                print("hierarchy -simcheck", file=f)
                print("write_ilang ../model/design{}.il".format("" if model_name == "base" else "_nomem"), file=f)

            task = SbyTask(self, model_name, [],
                    "cd {}/src; {} -ql ../model/design{s}.log ../model/design{s}.ys".format(self.workdir, self.exe_paths["yosys"],
                    s="" if model_name == "base" else "_nomem"))
            task.checkretcode = True

            return [task]

        if re.match(r"^smt2(_syn)?(_nomem)?(_stbv|_stdt)?$", model_name):
            with open("{}/model/design_{}.ys".format(self.workdir, model_name), "w") as f:
                print("# running in {}/model/".format(self.workdir), file=f)
                print("read_ilang design{}.il".format("_nomem" if "_nomem" in model_name else ""), file=f)
                if "_syn" in model_name:
                    print("techmap", file=f)
                    print("opt -fast", file=f)
                    print("abc", file=f)
                    print("opt_clean", file=f)
                print("dffunmap", file=f)
                print("stat", file=f)
                if "_stbv" in model_name:
                    print("write_smt2 -stbv -wires design_{}.smt2".format(model_name), file=f)
                elif "_stdt" in model_name:
                    print("write_smt2 -stdt -wires design_{}.smt2".format(model_name), file=f)
                else:
                    print("write_smt2 -wires design_{}.smt2".format(model_name), file=f)

            task = SbyTask(self, model_name, self.model("nomem" if "_nomem" in model_name else "base"),
                    "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name))
            task.checkretcode = True

            return [task]

        if re.match(r"^btor(_syn)?(_nomem)?$", model_name):
            with open("{}/model/design_{}.ys".format(self.workdir, model_name), "w") as f:
                print("# running in {}/model/".format(self.workdir), file=f)
                print("read_ilang design{}.il".format("_nomem" if "_nomem" in model_name else ""), file=f)
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
                print("write_btor {}-i design_{m}.info design_{m}.btor".format("-c " if self.opt_mode == "cover" else "", m=model_name), file=f)

            task = SbyTask(self, model_name, self.model("nomem" if "_nomem" in model_name else "base"),
                    "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name))
            task.checkretcode = True

            return [task]

        if model_name == "aig":
            with open("{}/model/design_aiger.ys".format(self.workdir), "w") as f:
                print("# running in {}/model/".format(self.workdir), file=f)
                print("read_ilang design_nomem.il", file=f)
                print("flatten", file=f)
                print("setundef -undriven -anyseq", file=f)
                print("setattr -unset keep", file=f)
                print("delete -output", file=f)
                print("opt -full", file=f)
                print("techmap", file=f)
                print("opt -fast", file=f)
                print("dffunmap", file=f)
                print("abc -g AND -fast", file=f)
                print("opt_clean", file=f)
                print("stat", file=f)
                print("write_aiger -I -B -zinit -map design_aiger.aim design_aiger.aig", file=f)

            task = SbyTask(self, "aig", self.model("nomem"),
                    "cd {}/model; {} -ql design_aiger.log design_aiger.ys".format(self.workdir, self.exe_paths["yosys"]))
            task.checkretcode = True

            return [task]

        assert False

    def model(self, model_name):
        if model_name not in self.models:
            self.models[model_name] = self.make_model(model_name)
        return self.models[model_name]

    def terminate(self, timeout=False):
        for task in list(self.tasks_running):
            task.terminate(timeout=timeout)

    def update_status(self, new_status):
        assert new_status in ["PASS", "FAIL", "UNKNOWN", "ERROR"]

        if new_status == "UNKNOWN":
            return

        if self.status == "ERROR":
            return

        if new_status == "PASS":
            assert self.status != "FAIL"
            self.status = "PASS"

        elif new_status == "FAIL":
            assert self.status != "PASS"
            self.status = "FAIL"

        elif new_status == "ERROR":
            self.status = "ERROR"

        else:
            assert 0

    def run(self, setupmode):
        mode = None
        key = None

        with open("{}/config.sby".format(self.workdir), "r") as f:
            for line in f:
                raw_line = line
                if mode in ["options", "engines", "files"]:
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
                    entries = match.group(1).split()
                    if len(entries) == 0:
                        self.error("sby file syntax error: {}".format(line))

                    if entries[0] == "options":
                        mode = "options"
                        if len(self.options) != 0 or len(entries) != 1:
                            self.error("sby file syntax error: {}".format(line))
                        continue

                    if entries[0] == "engines":
                        mode = "engines"
                        if len(self.engines) != 0 or len(entries) != 1:
                            self.error("sby file syntax error: {}".format(line))
                        continue

                    if entries[0] == "script":
                        mode = "script"
                        if len(self.script) != 0 or len(entries) != 1:
                            self.error("sby file syntax error: {}".format(line))
                        continue

                    if entries[0] == "file":
                        mode = "file"
                        if len(entries) != 2:
                            self.error("sby file syntax error: {}".format(line))
                        current_verbatim_file = entries[1]
                        if current_verbatim_file in self.verbatim_files:
                            self.error("duplicate file: {}".format(entries[1]))
                        self.verbatim_files[current_verbatim_file] = list()
                        continue

                    if entries[0] == "files":
                        mode = "files"
                        if len(entries) != 1:
                            self.error("sby file syntax error: {}".format(line))
                        continue

                    self.error("sby file syntax error: {}".format(line))

                if mode == "options":
                    entries = line.split()
                    if len(entries) != 2:
                        self.error("sby file syntax error: {}".format(line))
                    self.options[entries[0]] = entries[1]
                    continue

                if mode == "engines":
                    entries = line.split()
                    self.engines.append(entries)
                    continue

                if mode == "script":
                    self.script.append(line)
                    continue

                if mode == "files":
                    entries = line.split()
                    if len(entries) == 1:
                        self.files[os.path.basename(entries[0])] = entries[0]
                    elif len(entries) == 2:
                        self.files[entries[0]] = entries[1]
                    else:
                        self.error("sby file syntax error: {}".format(line))
                    continue

                if mode == "file":
                    self.verbatim_files[current_verbatim_file].append(raw_line)
                    continue

                self.error("sby file syntax error: {}".format(line))

        self.handle_str_option("mode", None)

        if self.opt_mode not in ["bmc", "prove", "cover", "live"]:
            self.error("Invalid mode: {}".format(self.opt_mode))

        self.expect = ["PASS"]
        if "expect" in self.options:
            self.expect = self.options["expect"].upper().split(",")
            self.used_options.add("expect")

        for s in self.expect:
            if s not in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]:
                self.error("Invalid expect value: {}".format(s))

        self.handle_bool_option("multiclock", False)
        self.handle_bool_option("wait", False)
        self.handle_int_option("timeout", None)

        self.handle_str_option("smtc", None)
        self.handle_int_option("skip", None)
        self.handle_str_option("tbtop", None)

        if self.opt_smtc is not None:
            for engine in self.engines:
                if engine[0] != "smtbmc":
                    self.error("Option smtc is only valid for smtbmc engine.")

        if self.opt_skip is not None:
            if self.opt_skip == 0:
                self.opt_skip = None
            else:
                for engine in self.engines:
                    if engine[0] not in ["smtbmc", "btor"]:
                        self.error("Option skip is only valid for smtbmc and btor engines.")

        if len(self.engines) == 0:
            self.error("Config file is lacking engine configuration.")

        if self.reusedir:
            rmtree("{}/model".format(self.workdir), ignore_errors=True)
        else:
            self.copy_src()

        if setupmode:
            self.retcode = 0
            return

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
                self.error("Unused option: {}".format(opt))

        self.taskloop()

        total_clock_time = int(time() - self.start_clock_time)

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            total_process_time = int((ru.ru_utime + ru.ru_stime) - self.start_process_time)
            self.total_time = total_process_time

            self.summary = [
                "Elapsed clock time [H:MM:SS (secs)]: {}:{:02d}:{:02d} ({})".format
                        (total_clock_time // (60*60), (total_clock_time // 60) % 60, total_clock_time % 60, total_clock_time),
                "Elapsed process time [H:MM:SS (secs)]: {}:{:02d}:{:02d} ({})".format
                        (total_process_time // (60*60), (total_process_time // 60) % 60, total_process_time % 60, total_process_time),
            ] + self.summary
        else:
            self.summary = [
                "Elapsed clock time [H:MM:SS (secs)]: {}:{:02d}:{:02d} ({})".format
                        (total_clock_time // (60*60), (total_clock_time // 60) % 60, total_clock_time % 60, total_clock_time),
                "Elapsed process time unvailable on Windows"
            ] + self.summary

        for line in self.summary:
            self.log("summary: {}".format(line))

        assert self.status in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]

        if self.status in self.expect:
            self.retcode = 0
        else:
            if self.status == "PASS": self.retcode = 1
            if self.status == "FAIL": self.retcode = 2
            if self.status == "UNKNOWN": self.retcode = 4
            if self.status == "TIMEOUT": self.retcode = 8
            if self.status == "ERROR": self.retcode = 16

        with open("{}/{}".format(self.workdir, self.status), "w") as f:
            for line in self.summary:
                print(line, file=f)
