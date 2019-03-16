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

import os, re, sys
if os.name == "posix":
    import resource, fcntl
import subprocess
from shutil import copyfile
from select import select
from time import time, localtime

class SbyTask:
    def __init__(self, job, info, deps, cmdline, logfile=None, logstderr=True):
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
            replacements = {
                ";" : "&",
                "{" : "(",
                "}" : ")",
            }

            cmdline_copy = cmdline
            for u, w in replacements.items():
                cmdline_copy = cmdline_copy.replace(u, w)
            self.cmdline = cmdline_copy
        self.logfile = logfile
        self.noprintregex = None
        self.notify = []
        self.linebuffer = ""
        self.logstderr = logstderr

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

    def handle_output(self, line):
        if self.terminated or len(line) == 0:
            return
        if self.output_callback is not None:
            line = self.output_callback(line)
        if line is not None and (self.noprintregex is None or not self.noprintregex.match(line)):
            if self.logfile is not None:
                print(line, file=self.logfile)
            self.job.log("%s: %s" % (self.info, line))

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
            self.job.log("%s: terminating process" % self.info)
            self.p.terminate()
            self.job.tasks_running.remove(self)
        self.terminated = True

    def poll(self):
        if self.finished or self.terminated:
            return

        if not self.running:
            for dep in self.deps:
                if not dep.finished:
                    return

            self.job.log("%s: starting process \"%s\"" % (self.info, self.cmdline))
            self.p = subprocess.Popen(self.cmdline, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                    stderr=(subprocess.STDOUT if self.logstderr else None))
            if os.name == "posix":
                fl = fcntl.fcntl(self.p.stdout, fcntl.F_GETFL)
                fcntl.fcntl(self.p.stdout, fcntl.F_SETFL, fl | os.O_NONBLOCK)
            self.job.tasks_pending.remove(self)
            self.job.tasks_running.append(self)
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
            self.job.log("%s: finished (returncode=%d)" % (self.info, self.p.returncode))
            self.job.tasks_running.remove(self)
            self.running = False

            self.handle_exit(self.p.returncode)

            if self.checkretcode and self.p.returncode != 0:
                self.job.status = "ERROR"
                self.job.log("%s: job failed. ERROR." % self.info)
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

        self.exe_paths = {
            "yosys": "yosys",
            "abc": "yosys-abc",
            "smtbmc": "yosys-smtbmc",
            "suprove": "suprove",
            "aigbmc": "aigbmc",
            "avy": "avy",
            "btormc": "btormc",
        }

        self.tasks_running = []
        self.tasks_pending = []

        self.start_clock_time = time()

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            self.start_process_time = ru.ru_utime + ru.ru_stime

        self.summary = list()

        self.logfile = open("%s/logfile.txt" % workdir, "a")

        for line in early_logs:
            print(line, file=self.logfile)
        self.logfile.flush()

        with open("%s/config.sby" % workdir, "w") as f:
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

            try:
                select(fds, [], [], 1.0) == ([], [], [])
            except:
                pass

            for task in self.tasks_running:
                task.poll()

            for task in self.tasks_pending:
                task.poll()

            if self.opt_timeout is not None:
                total_clock_time = int(time() - self.start_clock_time)
                if total_clock_time > self.opt_timeout:
                    self.log("Reached TIMEOUT (%d seconds). Terminating all tasks." % self.opt_timeout)
                    self.status = "TIMEOUT"
                    self.terminate(timeout=True)

    def log(self, logmessage):
        tm = localtime()
        print("SBY %2d:%02d:%02d [%s] %s" % (tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage))
        print("SBY %2d:%02d:%02d [%s] %s" % (tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage), file=self.logfile)
        self.logfile.flush()

    def error(self, logmessage):
        tm = localtime()
        print("SBY %2d:%02d:%02d [%s] ERROR: %s" % (tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage))
        print("SBY %2d:%02d:%02d [%s] ERROR: %s" % (tm.tm_hour, tm.tm_min, tm.tm_sec, self.workdir, logmessage), file=self.logfile)
        self.logfile.flush()
        self.status = "ERROR"
        if "ERROR" not in self.expect:
            self.retcode = 16
        self.terminate()
        with open("%s/%s" % (self.workdir, self.status), "w") as f:
            print("ERROR: %s" % logmessage, file=f)
        raise SbyAbort(logmessage)

    def makedirs(self, path):
        if self.reusedir and os.path.isdir(path):
            rmtree(path, ignore_errors=True)
        os.makedirs(path)

    def copy_src(self):
        os.makedirs(self.workdir + "/src")

        for dstfile, lines in self.verbatim_files.items():
            dstfile = self.workdir + "/src/" + dstfile
            self.log("Writing '%s'." % dstfile)

            with open(dstfile, "w") as f:
                for line in lines:
                    f.write(line)

        for dstfile, srcfile in self.files.items():
            if dstfile.startswith("/") or dstfile.startswith("../") or ("/../" in dstfile):
                self.error("destination filename must be a relative path without /../: %s" % dstfile)
            dstfile = self.workdir + "/src/" + dstfile

            if srcfile.startswith("~/"):
                srcfile = os.environ['HOME'] + srcfile[1:]

            basedir = os.path.dirname(dstfile)
            if basedir != "" and not os.path.exists(basedir):
                os.makedirs(basedir)

            self.log("Copy '%s' to '%s'." % (srcfile, dstfile))
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
                self.error("Invalid value '%s' for boolean option %s." % (self.options[option_name], option_name))
            self.__dict__["opt_" + option_name] = self.options[option_name] == "on"
            self.used_options.add(option_name)
        else:
            self.__dict__["opt_" + option_name] = default_value

    def make_model(self, model_name):
        if not os.path.isdir("%s/model" % self.workdir):
            os.makedirs("%s/model" % self.workdir)

        if model_name in ["base", "nomem"]:
            with open("%s/model/design%s.ys" % (self.workdir, "" if model_name == "base" else "_nomem"), "w") as f:
                print("# running in %s/src/" % self.workdir, file=f)
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
                print("write_ilang ../model/design%s.il" % ("" if model_name == "base" else "_nomem"), file=f)

            task = SbyTask(self, model_name, [],
                    "cd %s/src; %s -ql ../model/design%s.log ../model/design%s.ys" % (self.workdir, self.exe_paths["yosys"],
                    "" if model_name == "base" else "_nomem", "" if model_name == "base" else "_nomem"))
            task.checkretcode = True

            return [task]

        if re.match(r"^smt2(_syn)?(_nomem)?(_stbv|_stdt)?$", model_name):
            with open("%s/model/design_%s.ys" % (self.workdir, model_name), "w") as f:
                print("# running in %s/model/" % (self.workdir), file=f)
                print("read_ilang design%s.il" % ("_nomem" if "_nomem" in model_name else ""), file=f)
                if "_syn" in model_name:
                    print("techmap", file=f)
                    print("opt -fast", file=f)
                    print("abc", file=f)
                    print("opt_clean", file=f)
                print("stat", file=f)
                if "_stbv" in model_name:
                    print("write_smt2 -stbv -wires design_%s.smt2" % model_name, file=f)
                elif "_stdt" in model_name:
                    print("write_smt2 -stdt -wires design_%s.smt2" % model_name, file=f)
                else:
                    print("write_smt2 -wires design_%s.smt2" % model_name, file=f)

            task = SbyTask(self, model_name, self.model("nomem" if "_nomem" in model_name else "base"),
                    "cd %s/model; %s -ql design_%s.log design_%s.ys" % (self.workdir, self.exe_paths["yosys"], model_name, model_name))
            task.checkretcode = True

            return [task]

        if re.match(r"^btor(_syn)?(_nomem)?$", model_name):
            with open("%s/model/design_%s.ys" % (self.workdir, model_name), "w") as f:
                print("# running in %s/model/" % (self.workdir), file=f)
                print("read_ilang design%s.il" % ("_nomem" if "_nomem" in model_name else ""), file=f)
                print("flatten", file=f)
                print("setattr -unset keep", file=f)
                print("delete -output", file=f)
                print("opt -full", file=f)
                if "_syn" in model_name:
                    print("techmap", file=f)
                    print("opt -fast", file=f)
                    print("abc", file=f)
                    print("opt_clean", file=f)
                print("stat", file=f)
                print("write_btor design_%s.btor" % model_name, file=f)

            task = SbyTask(self, model_name, self.model("nomem" if "_nomem" in model_name else "base"),
                    "cd %s/model; %s -ql design_%s.log design_%s.ys" % (self.workdir, self.exe_paths["yosys"], model_name, model_name))
            task.checkretcode = True

            return [task]

        if model_name == "aig":
            with open("%s/model/design_aiger.ys" % (self.workdir), "w") as f:
                print("# running in %s/model/" % (self.workdir), file=f)
                print("read_ilang design_nomem.il", file=f)
                print("flatten", file=f)
                print("setattr -unset keep", file=f)
                print("delete -output", file=f)
                print("opt -full", file=f)
                print("techmap", file=f)
                print("opt -fast", file=f)
                print("abc -g AND -fast", file=f)
                print("opt_clean", file=f)
                print("stat", file=f)
                print("write_aiger -I -B -zinit -map design_aiger.aim design_aiger.aig", file=f)

            task = SbyTask(self, "aig", self.model("nomem"),
                    "cd %s/model; %s -ql design_aiger.log design_aiger.ys" % (self.workdir, self.exe_paths["yosys"]))
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

        with open("%s/config.sby" % self.workdir, "r") as f:
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
                        self.error("sby file syntax error: %s" % line)

                    if entries[0] == "options":
                        mode = "options"
                        if len(self.options) != 0 or len(entries) != 1:
                            self.error("sby file syntax error: %s" % line)
                        continue

                    if entries[0] == "engines":
                        mode = "engines"
                        if len(self.engines) != 0 or len(entries) != 1:
                            self.error("sby file syntax error: %s" % line)
                        continue

                    if entries[0] == "script":
                        mode = "script"
                        if len(self.script) != 0 or len(entries) != 1:
                            self.error("sby file syntax error: %s" % line)
                        continue

                    if entries[0] == "file":
                        mode = "file"
                        if len(entries) != 2:
                            self.error("sby file syntax error: %s" % line)
                        current_verbatim_file = entries[1]
                        if current_verbatim_file in self.verbatim_files:
                            self.error("duplicate file: %s" % entries[1])
                        self.verbatim_files[current_verbatim_file] = list()
                        continue

                    if entries[0] == "files":
                        mode = "files"
                        if len(entries) != 1:
                            self.error("sby file syntax error: %s" % line)
                        continue

                    self.error("sby file syntax error: %s" % line)

                if mode == "options":
                    entries = line.split()
                    if len(entries) != 2:
                        self.error("sby file syntax error: %s" % line)
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
                        self.error("sby file syntax error: %s" % line)
                    continue

                if mode == "file":
                    self.verbatim_files[current_verbatim_file].append(raw_line)
                    continue

                self.error("sby file syntax error: %s" % line)

        self.handle_str_option("mode", None)

        if self.opt_mode not in ["bmc", "prove", "cover", "live"]:
            self.error("Invalid mode: %s" % self.opt_mode)

        self.expect = ["PASS"]
        if "expect" in self.options:
            self.expect = self.options["expect"].upper().split(",")
            self.used_options.add("expect")

        for s in self.expect:
            if s not in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]:
                self.error("Invalid expect value: %s" % s)

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

        if self.reusedir:
            rmtree("%s/model" % self.workdir, ignore_errors=True)
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
                self.error("Unused option: %s" % opt)

        self.taskloop()

        total_clock_time = int(time() - self.start_clock_time)

        if os.name == "posix":
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            total_process_time = int((ru.ru_utime + ru.ru_stime) - self.start_process_time)
            self.total_time = total_process_time
        else:
            total_process_time = 0

        self.summary = [
            "Elapsed clock time [H:MM:SS (secs)]: %d:%02d:%02d (%d)" %
                    (total_clock_time // (60*60), (total_clock_time // 60) % 60, total_clock_time % 60, total_clock_time),
            "Elapsed process time [H:MM:SS (secs)]: %d:%02d:%02d (%d)" %
                    (total_process_time // (60*60), (total_process_time // 60) % 60, total_process_time % 60, total_process_time),
        ] + self.summary

        for line in self.summary:
            self.log("summary: %s" % line)

        assert self.status in ["PASS", "FAIL", "UNKNOWN", "ERROR", "TIMEOUT"]

        if self.status in self.expect:
            self.retcode = 0
        else:
            if self.status == "PASS": self.retcode = 1
            if self.status == "FAIL": self.retcode = 2
            if self.status == "UNKNOWN": self.retcode = 4
            if self.status == "TIMEOUT": self.retcode = 8
            if self.status == "ERROR": self.retcode = 16

        with open("%s/%s" % (self.workdir, self.status), "w") as f:
            for line in self.summary:
                print(line, file=f)
