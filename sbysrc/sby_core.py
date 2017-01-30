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

import os, re, resource
import subprocess, fcntl
from shutil import copyfile
from select import select
from time import time

class SbyTask:
    def __init__(self, job, info, deps, cmdline, logfile=None):
        self.running = False
        self.finished = False
        self.terminated = False
        self.checkretcode = False
        self.job = job
        self.info = info
        self.deps = deps
        self.cmdline = cmdline
        self.logfile = logfile
        self.notify = []

        for dep in self.deps:
            dep.register_dep(self)

        self.output_callback = None
        self.exit_callback = None

        self.job.tasks_all.append(self)

    def register_dep(self, next_task):
        if self.finished:
            next_task.poll()
        else:
            self.notify.append(next_task)

    def handle_output(self, line):
        if self.terminated:
            return
        if self.logfile is not None:
            print(line, file=self.logfile)
        if self.output_callback is not None:
            self.output_callback(line)

    def handle_exit(self, retcode):
        if self.terminated:
            return
        if self.logfile is not None:
            self.logfile.close()
        if self.exit_callback is not None:
            self.exit_callback(retcode)

    def terminate(self):
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
            self.p = subprocess.Popen(self.cmdline, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            fl = fcntl.fcntl(self.p.stdout, fcntl.F_GETFL)
            fcntl.fcntl(self.p.stdout, fcntl.F_SETFL, fl | os.O_NONBLOCK)
            self.job.tasks_running.append(self)
            self.running = True
            return

        while True:
            outs = self.p.stdout.readline().decode("utf-8")
            if len(outs) == 0: break
            self.job.log("%s: %s" % (self.info, outs.strip()))
            self.handle_output(outs.strip())

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


class SbyJob:
    def __init__(self, filename, workdir, early_logs):
        self.options = dict()
        self.engines = list()
        self.script = list()
        self.files = dict()
        self.models = dict()
        self.workdir = workdir

        self.status = None
        self.tasks_running = []
        self.tasks_all = []

        self.start_clock_time = time()

        ru = resource.getrusage(resource.RUSAGE_CHILDREN)
        self.start_process_time = ru.ru_utime + ru.ru_stime

        self.logprefix = "SBY [%s]" % self.workdir
        self.summary = list()

        os.makedirs(workdir)
        self.logfile = open("%s/logfile.txt" % workdir, "w")

        for line in early_logs:
            print(line, file=self.logfile)
        self.logfile.flush()

        mode = None
        key = None

        with open(filename, "r") as f:
            for line in f:
                line = line.strip()
                # print(line)

                if line == "" or line[0] == "#":
                    continue

                match = re.match(r"^\s*\[(.*)\]\s*$", line)
                if match:
                    entries = match.group(1).split()
                    assert len(entries) > 0

                    if entries[0] == "options":
                        mode = "options"
                        assert len(self.options) == 0
                        assert len(entries) == 1
                        continue

                    if entries[0] == "engines":
                        mode = "engines"
                        assert len(self.engines) == 0
                        assert len(entries) == 1
                        continue

                    if entries[0] == "script":
                        mode = "script"
                        assert len(self.script) == 0
                        assert len(entries) == 1
                        continue

                    if entries[0] == "files":
                        mode = "files"
                        assert len(entries) == 1
                        continue

                    assert False

                if mode == "options":
                    entries = line.split()
                    assert len(entries) == 2
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
                        assert False
                    continue

                assert False

    def taskloop(self):
        for task in self.tasks_all:
            task.poll()

        while len(self.tasks_running):
            fds = []
            for task in self.tasks_running:
                if task.running:
                    fds.append(task.p.stdout)

            try:
                while select(fds, [], [], 1.0) == ([], [], []):
                    pass
            except:
                pass

            for task in self.tasks_running:
                task.poll()

    def log(self, logmessage):
        print("%s %s" % (self.logprefix, logmessage))
        print("%s %s" % (self.logprefix, logmessage), file=self.logfile)
        self.logfile.flush()

    def copy_src(self):
        os.makedirs(self.workdir + "/src")

        for dstfile, srcfile in self.files.items():
            dstfile = self.workdir + "/src/" + dstfile

            if srcfile.startswith("~/"):
                srcfile = os.environ['HOME'] + srcfile[1:]

            basedir = os.path.dirname(dstfile)
            if basedir != "" and not os.path.exists(basedir):
                os.makedirs(basedir)

            self.log("Copy '%s' to '%s'." % (srcfile, dstfile))
            copyfile(srcfile, dstfile)

    def make_model(self, model_name):
        if not os.path.exists("%s/model" % self.workdir):
            os.makedirs("%s/model" % self.workdir)

        if model_name == "ilang":
            with open("%s/model/design.ys" % (self.workdir), "w") as f:
                print("# running in %s/src/" % self.workdir, file=f)
                for cmd in self.script:
                    print(cmd, file=f)
                print("write_ilang ../model/design.il", file=f)

            task = SbyTask(self, "script", [],
                    "cd %s/src; yosys -ql ../model/design.log ../model/design.ys" % (self.workdir))
            task.checkretcode = True

            return [task]

        if model_name in ["smt2", "smt2_syn", "smt2_nomem", "smt2_syn_nomem"]:
            with open("%s/model/design_%s.ys" % (self.workdir, model_name), "w") as f:
                print("# running in %s/model/" % (self.workdir), file=f)
                print("read_ilang design.il", file=f)
                if model_name in ["smt2_nomem", "smt2_syn_nomem"]:
                    print("memory_map", file=f)
                    print("opt -keepdc -fast", file=f)
                if model_name in ["smt2_syn", "smt2_syn_nomem"]:
                    print("techmap", file=f)
                    print("opt -fast", file=f)
                    print("abc", file=f)
                    print("opt_clean", file=f)
                print("stat", file=f)
                print("write_smt2 -wires design_%s.smt2" % model_name, file=f)

            task = SbyTask(self, model_name, self.model("ilang"),
                    "cd %s/model; yosys -ql design_%s.log design_%s.ys" % (self.workdir, model_name, model_name))
            task.checkretcode = True

            return [task]

        if model_name == "aig":
            with open("%s/model/design_aiger.ys" % (self.workdir), "w") as f:
                print("# running in %s/model/" % (self.workdir), file=f)
                print("read_ilang design.il", file=f)
                print("flatten", file=f)
                print("setattr -unset keep", file=f)
                print("delete -output", file=f)
                print("opt -full", file=f)
                print("memory_map", file=f)
                print("opt -fast", file=f)
                print("techmap", file=f)
                print("opt -fast", file=f)
                print("abc -g AND -fast", file=f)
                print("opt_clean", file=f)
                print("stat", file=f)
                print("write_aiger -zinit -map design_aiger.aim design_aiger.aig", file=f)

            task = SbyTask(self, "aig", self.model("ilang"),
                    "cd %s/model; yosys -ql design_aiger.log design_aiger.ys" % (self.workdir))
            task.checkretcode = True

            return [task]

        assert False

    def model(self, model_name):
        if model_name not in self.models:
            self.models[model_name] = self.make_model(model_name)
        return self.models[model_name]

    def terminate(self):
        for task in self.tasks_running:
            task.terminate()

    def run(self):
        assert "mode" in self.options

        self.copy_src()

        if self.options["mode"] == "bmc":
            import sby_mode_bmc
            sby_mode_bmc.run(self)

        else:
            assert False

        total_clock_time = int(time() - self.start_clock_time)

        ru = resource.getrusage(resource.RUSAGE_CHILDREN)
        total_process_time = int((ru.ru_utime + ru.ru_stime) - self.start_process_time)

        self.summary = [
            "Elapsed clock time [H:MM:SS (secs)]: %d:%02d:%02d (%d)" %
                    (total_clock_time // (60*60), (total_clock_time // 60) % 60, total_clock_time % 60, total_clock_time),
            "Elapsed process time [H:MM:SS (secs)]: %d:%02d:%02d (%d)" %
                    (total_process_time // (60*60), (total_process_time // 60) % 60, total_process_time % 60, total_process_time),
        ] + self.summary

        for line in self.summary:
            self.log("summary: %s" % line)

        self.log("DONE (%s)" % self.status)
        assert self.status in ["PASS", "FAIL", "UNKNOWN", "ERROR"]

        with open("%s/%s" % (self.workdir, self.status), "w") as f:
            for line in self.summary:
                print(line, file=f)

