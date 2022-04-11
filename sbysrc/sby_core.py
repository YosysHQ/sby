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

import os, re, sys, signal, platform
if os.name == "posix":
    import resource, fcntl
import subprocess
from shutil import copyfile, copytree, rmtree
from select import select
from time import time, localtime, sleep, strftime
from sby_design import SbyProperty, SbyModule, design_hierarchy

all_procs_running = []

def force_shutdown(signum, frame):
    print("SBY ---- Keyboard interrupt or external termination signal ----", flush=True)
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

class SbyProc:
    def __init__(self, task, info, deps, cmdline, logfile=None, logstderr=True, silent=False):
        self.running = False
        self.finished = False
        self.terminated = False
        self.checkretcode = False
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

        self.task.procs_pending.append(self)

        for dep in self.deps:
            dep.register_dep(self)

        self.output_callback = None
        self.exit_callback = None

    def register_dep(self, next_proc):
        if self.finished:
            next_proc.poll()
        else:
            self.notify.append(next_proc)

    def log(self, line):
        if line is not None and (self.noprintregex is None or not self.noprintregex.match(line)):
            if self.logfile is not None:
                print(line, file=self.logfile)
            self.task.log(f"{self.info}: {line}")

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
        if self.task.opt_wait and not timeout:
            return
        if self.running:
            if not self.silent:
                self.task.log(f"{self.info}: terminating process")
            if os.name == "posix":
                try:
                    os.killpg(self.p.pid, signal.SIGTERM)
                except PermissionError:
                    pass
            self.p.terminate()
            self.task.procs_running.remove(self)
            all_procs_running.remove(self)
        self.terminated = True

    def poll(self):
        if self.finished or self.terminated:
            return

        if not self.running:
            for dep in self.deps:
                if not dep.finished:
                    return

            if not self.silent:
                self.task.log(f"{self.info}: starting process \"{self.cmdline}\"")

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

            self.task.procs_pending.remove(self)
            self.task.procs_running.append(self)
            all_procs_running.append(self)
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
                self.task.log(f"{self.info}: finished (returncode={self.p.returncode})")
            self.task.procs_running.remove(self)
            all_procs_running.remove(self)
            self.running = False

            if self.p.returncode == 127:
                self.task.status = "ERROR"
                if not self.silent:
                    self.task.log(f"{self.info}: COMMAND NOT FOUND. ERROR.")
                self.terminated = True
                self.task.terminate()
                return

            self.handle_exit(self.p.returncode)

            if self.checkretcode and self.p.returncode != 0:
                self.task.status = "ERROR"
                if not self.silent:
                    self.task.log(f"{self.info}: task failed. ERROR.")
                self.terminated = True
                self.task.terminate()
                return

            self.finished = True
            for next_proc in self.notify:
                next_proc.poll()
            return


class SbyAbort(BaseException):
    pass


class SbyConfig:
    def __init__(self):
        self.options = dict()
        self.engines = list()
        self.script = list()
        self.files = dict()
        self.verbatim_files = dict()
        pass

    def parse_config(self, f):
        mode = None

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
                    self.error(f"sby file syntax error: {line}")

                if entries[0] == "options":
                    mode = "options"
                    if len(self.options) != 0 or len(entries) != 1:
                        self.error(f"sby file syntax error: {line}")
                    continue

                if entries[0] == "engines":
                    mode = "engines"
                    if len(self.engines) != 0 or len(entries) != 1:
                        self.error(f"sby file syntax error: {line}")
                    continue

                if entries[0] == "script":
                    mode = "script"
                    if len(self.script) != 0 or len(entries) != 1:
                        self.error(f"sby file syntax error: {line}")
                    continue

                if entries[0] == "file":
                    mode = "file"
                    if len(entries) != 2:
                        self.error(f"sby file syntax error: {line}")
                    current_verbatim_file = entries[1]
                    if current_verbatim_file in self.verbatim_files:
                        self.error(f"duplicate file: {entries[1]}")
                    self.verbatim_files[current_verbatim_file] = list()
                    continue

                if entries[0] == "files":
                    mode = "files"
                    if len(entries) != 1:
                        self.error(f"sby file syntax error: {line}")
                    continue

                self.error(f"sby file syntax error: {line}")

            if mode == "options":
                entries = line.split()
                if len(entries) != 2:
                    self.error(f"sby file syntax error: {line}")
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
                    self.error(f"sby file syntax error: {line}")
                continue

            if mode == "file":
                self.verbatim_files[current_verbatim_file].append(raw_line)
                continue

            self.error(f"sby file syntax error: {line}")

    def error(self, logmessage):
        raise SbyAbort(logmessage)

class SbyTask(SbyConfig):
    def __init__(self, sbyconfig, workdir, early_logs, reusedir):
        super().__init__()
        self.used_options = set()
        self.models = dict()
        self.workdir = workdir
        self.reusedir = reusedir
        self.status = "UNKNOWN"
        self.total_time = 0
        self.expect = list()
        self.design_hierarchy = None
        self.precise_prop_status = False

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

        self.procs_running = []
        self.procs_pending = []

        self.start_clock_time = time()

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            self.start_process_time = ru.ru_utime + ru.ru_stime

        self.summary = list()

        self.logfile = open(f"{workdir}/logfile.txt", "a")

        for line in early_logs:
            print(line, file=self.logfile, flush=True)

        if not reusedir:
            with open(f"{workdir}/config.sby", "w") as f:
                for line in sbyconfig:
                    print(line, file=f)

    def taskloop(self):
        for proc in self.procs_pending:
            proc.poll()

        while len(self.procs_running):
            fds = []
            for proc in self.procs_running:
                if proc.running:
                    fds.append(proc.p.stdout)

            if os.name == "posix":
                try:
                    select(fds, [], [], 1.0) == ([], [], [])
                except InterruptedError:
                    pass
            else:
                sleep(0.1)

            for proc in self.procs_running:
                proc.poll()

            for proc in self.procs_pending:
                proc.poll()

            if self.opt_timeout is not None:
                total_clock_time = int(time() - self.start_clock_time)
                if total_clock_time > self.opt_timeout:
                    self.log(f"Reached TIMEOUT ({self.opt_timeout} seconds). Terminating all subprocesses.")
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
        else:
            self.retcode = 0
        self.terminate()
        with open(f"{self.workdir}/{self.status}", "w") as f:
            print(f"ERROR: {logmessage}", file=f)
        raise SbyAbort(logmessage)

    def makedirs(self, path):
        if self.reusedir and os.path.isdir(path):
            rmtree(path, ignore_errors=True)
        os.makedirs(path)

    def copy_src(self):
        os.makedirs(self.workdir + "/src")

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

        def print_common_prep():
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

        if model_name == "base":
            with open(f"""{self.workdir}/model/design.ys""", "w") as f:
                print(f"# running in {self.workdir}/src/", file=f)
                for cmd in self.script:
                    print(cmd, file=f)
                # the user must designate a top module in [script]
                print("hierarchy -simcheck", file=f)
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
                if retcode != 0:
                    self.precise_prop_status = False
                    return
                if self.design_hierarchy == None:
                    with open(f"{self.workdir}/model/design.json") as f:
                        self.design_hierarchy = design_hierarchy(f)

            proc.exit_callback = instance_hierarchy_callback

            return [proc]

        if re.match(r"^smt2(_syn)?(_nomem)?(_stbv|_stdt)?$", model_name):
            with open(f"{self.workdir}/model/design_{model_name}.ys", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print(f"""read_ilang design.il""", file=f)
                if "_nomem" in model_name:
                    print("memory_map", file=f)
                else:
                    print("memory_nordff", file=f)
                print_common_prep()
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
                self.model("base"),
                "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name)
            )
            proc.checkretcode = True

            return [proc]

        if re.match(r"^btor(_syn)?(_nomem)?$", model_name):
            with open(f"{self.workdir}/model/design_{model_name}.ys", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print(f"""read_ilang design.il""", file=f)
                if "_nomem" in model_name:
                    print("memory_map", file=f)
                else:
                    print("memory_nordff", file=f)
                print_common_prep()
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
                print("write_btor -s {}-i design_{m}_single.info design_{m}_single.btor".format("-c " if self.opt_mode == "cover" else "", m=model_name), file=f)

            proc = SbyProc(
                self,
                model_name,
                self.model("base"),
                "cd {}/model; {} -ql design_{s}.log design_{s}.ys".format(self.workdir, self.exe_paths["yosys"], s=model_name)
            )
            proc.checkretcode = True

            return [proc]

        if model_name == "aig":
            with open(f"{self.workdir}/model/design_aiger.ys", "w") as f:
                print(f"# running in {self.workdir}/model/", file=f)
                print("read_ilang design.il", file=f)
                print("memory_map", file=f)
                print_common_prep()
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
                print("write_aiger -I -B -zinit -no-startoffset -map design_aiger.aim design_aiger.aig", file=f)

            proc = SbyProc(
                self,
                "aig",
                self.model("base"),
                f"""cd {self.workdir}/model; {self.exe_paths["yosys"]} -ql design_aiger.log design_aiger.ys"""
            )
            proc.checkretcode = True

            return [proc]

        assert False

    def model(self, model_name):
        if model_name not in self.models:
            self.models[model_name] = self.make_model(model_name)
        return self.models[model_name]

    def terminate(self, timeout=False):
        for proc in list(self.procs_running):
            proc.terminate(timeout=timeout)

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
            rmtree(f"{self.workdir}/model", ignore_errors=True)
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
                self.error(f"Unused option: {opt}")

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
            self.log(f"summary: {line}")

        assert self.status in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]

        if self.status in self.expect:
            self.retcode = 0
        else:
            if self.status == "PASS": self.retcode = 1
            if self.status == "FAIL": self.retcode = 2
            if self.status == "UNKNOWN": self.retcode = 4
            if self.status == "TIMEOUT": self.retcode = 8
            if self.status == "ERROR": self.retcode = 16

        with open(f"{self.workdir}/{self.status}", "w") as f:
            for line in self.summary:
                print(line, file=f)

    def print_junit_result(self, f, junit_ts_name, junit_tc_name, junit_format_strict=False):
        junit_time = strftime('%Y-%m-%dT%H:%M:%S')
        if self.precise_prop_status:
            checks = self.design_hierarchy.get_property_list()
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
