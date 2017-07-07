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

import re, os, getopt
from sby_core import SbyTask

def run(mode, job, engine_idx, engine):
    smtbmc_opts = []
    nomem_opt = False
    syn_opt = False
    stbv_opt = False

    opts, args = getopt.getopt(engine[1:], "", ["nomem", "syn", "stbv", "presat"])

    for o, a in opts:
        if o == "--nomem":
            nomem_opt = True
        elif o == "--syn":
            syn_opt = True
        elif o == "--stbv":
            stbv_opt = True
        elif o == "--presat":
            smtbmc_opts += ["--presat"]
        else:
            assert False

    for i, a in enumerate(args):
        smtbmc_opts += ["-s" if i == 0 else "-S", a]

    if job.opt_smtc is not None:
        smtbmc_opts += ["--smtc", "src/%s" % job.opt_smtc]

    if job.opt_tbtop is not None:
         smtbmc_opts += ["--vlogtb-top", job.opt_tbtop]

    model_name = "smt2"
    if syn_opt: model_name += "_syn"
    if nomem_opt: model_name += "_nomem"
    if stbv_opt: model_name += "_stbv"

    if mode == "prove":
        run("prove_basecase", job, engine_idx, engine)
        run("prove_induction", job, engine_idx, engine)
        return

    taskname = "engine_%d" % engine_idx
    trace_prefix = "engine_%d/trace" % engine_idx
    logfile_prefix = "%s/engine_%d/logfile" % (job.workdir, engine_idx)

    if mode == "prove_basecase":
        taskname += ".basecase"
        logfile_prefix += "_basecase"

    if mode == "prove_induction":
        taskname += ".induction"
        trace_prefix += "_induct"
        logfile_prefix += "_induction"
        smtbmc_opts.append("-i")

    if mode == "cover":
        smtbmc_opts.append("-c")
        trace_prefix += "%"

    task = SbyTask(job, taskname, job.model(model_name),
            "cd %s; %s --noprogress %s -t %d --append %d --dump-vcd %s.vcd --dump-vlogtb %s_tb.v --dump-smtc %s.smtc model/design_%s.smt2" %
                    (job.workdir, job.exe_paths["smtbmc"], " ".join(smtbmc_opts), job.opt_depth, job.opt_append, trace_prefix, trace_prefix, trace_prefix, model_name),
            logfile=open(logfile_prefix + ".txt", "w"))

    if mode == "prove_basecase":
        job.basecase_tasks.append(task)

    if mode == "prove_induction":
        job.induction_tasks.append(task)

    task_status = None

    def output_callback(line):
        nonlocal task_status

        match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
        if match: task_status = "FAIL"

        match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
        if match: task_status = "PASS"

        return line

    def exit_callback(retcode):
        assert task_status is not None

        if mode == "bmc" or mode == "cover":
            job.update_status(task_status)
            job.log("engine_%d: Status returned by engine: %s" % (engine_idx, task_status))
            job.summary.append("engine_%d (%s) returned %s" % (engine_idx, " ".join(engine), task_status))

            if task_status == "FAIL" and mode != "cover":
                job.summary.append("counterexample trace: %s/engine_%d/trace.vcd" % (job.workdir, engine_idx))

            job.terminate()

        elif mode in ["prove_basecase", "prove_induction"]:
            job.log("engine_%d: Status returned by engine for %s: %s" % (engine_idx, mode.split("_")[1], task_status))
            job.summary.append("engine_%d (%s) returned %s for %s" % (engine_idx, " ".join(engine), task_status, mode.split("_")[1]))

            if mode == "prove_basecase":
                for task in job.basecase_tasks:
                    task.terminate()

                if task_status == "PASS":
                    job.basecase_pass = True

                else:
                    job.update_status(task_status)
                    job.summary.append("counterexample trace: %s/engine_%d/trace.vcd" % (job.workdir, engine_idx))
                    job.terminate()

            elif mode == "prove_induction":
                for task in job.induction_tasks:
                    task.terminate()

                if task_status == "PASS":
                    job.induction_pass = True

            else:
                assert False

            if job.basecase_pass and job.induction_pass:
                job.update_status("PASS")
                job.summary.append("successful proof by k-induction.")
                job.terminate()

        else:
            assert False

    task.output_callback = output_callback
    task.exit_callback = exit_callback


