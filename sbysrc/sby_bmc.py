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
from shutil import copyfile
from sby_core import SbyTask

def run_smtbmc(job, engine_idx, engine):
    smtbmc_opts = []
    nomem_opt = False
    syn_opt = False

    opts, args = getopt.getopt(engine[1:], "s:", ["nomem", "syn"])
    assert len(args) == 0

    for o, a in opts:
        if o == "-s":
            smtbmc_opts += ["-s", a]
        elif o == "--nomem":
            nomem_opt = True
        elif o == "--syn":
            syn_opt = True
        else:
            assert False

    model_name = "smt2"
    if syn_opt: model_name += "_syn"
    if nomem_opt: model_name += "_nomem"

    task = SbyTask(job, "engine_%d" % engine_idx, job.model(model_name),
            ("cd %s; yosys-smtbmc --noprogress %s -t %d --dump-vcd engine_%d/trace.vcd --dump-vlogtb engine_%d/trace_tb.v " +
             "--dump-smtc engine_%d/trace.smtc model/design_smt2.smt2") %
                    (job.workdir, " ".join(smtbmc_opts), job.opt_depth, engine_idx, engine_idx, engine_idx),
            logfile=open("%s/engine_%d/logfile.txt" % (job.workdir, engine_idx), "w"))

    task_status = None

    def output_callback(line):
        nonlocal task_status

        match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
        if match: task_status = "FAIL"

        match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
        if match: task_status = "PASS"

    def exit_callback(retcode):
        assert task_status is not None

        job.status = task_status
        job.log("engine_%d: Status returned by engine: %s" % (engine_idx, task_status))
        job.summary.append("engine_%d (%s) returned %s" % (engine_idx, " ".join(engine), job.status))

        if job.status == "FAIL":
            job.summary.append("counterexample trace: %s/engine_%d/trace.vcd" % (job.workdir, engine_idx))

        for t in job.engine_tasks:
            if task is not t:
                t.terminate()

    task.output_callback = output_callback
    task.exit_callback = exit_callback
    job.engine_tasks.append(task)


def run_abc(job, engine_idx, engine):
    assert engine == ["abc", "bmc3"]

    task = SbyTask(job, "engine_%d" % engine_idx, job.model("aig"),
            ("cd %s; yosys-abc -c 'read_aiger model/design_aiger.aig; fold; strash; bmc3 -F %d -v; " +
             "undc -c; write_cex -a engine_%d/trace.aiw'") % (job.workdir, job.opt_depth, engine_idx),
            logfile=open("%s/engine_%d/logfile.txt" % (job.workdir, engine_idx), "w"))

    task_status = None

    def output_callback(line):
        nonlocal task_status

        match = re.match(r"^Output [0-9]+ of miter .* was asserted in frame [0-9]+.", line)
        if match: task_status = "FAIL"

        match = re.match(r"^Stopping BMC because all 2\^[0-9]+ reachable states are visited.", line)
        if match: task_status = "PASS"

        match = re.match(r"^No output asserted in [0-9]+ frames.", line)
        if match: task_status = "PASS"

    def exit_callback(retcode):
        assert retcode == 0
        assert task_status is not None

        job.status = task_status
        job.log("engine_%d: Status returned by engine: %s" % (engine_idx, task_status))
        job.summary.append("engine_%d (%s) returned %s" % (engine_idx, " ".join(engine), job.status))

        for t in job.engine_tasks:
            if task is not t:
                t.terminate()

        if job.status == "FAIL":
            copyfile("%s/model/design_aiger.aim" % job.workdir, "%s/engine_%d/trace.aim" % (job.workdir, engine_idx))
            task2 = SbyTask(job, "engine_%d" % engine_idx, job.model("smt2"),
                    ("cd %s; yosys-smtbmc --noprogress -t %d --dump-vcd engine_%d/trace.vcd --dump-vlogtb engine_%d/trace_tb.v " +
                     "--dump-smtc engine_%d/trace.smtc --aig engine_%d/trace --aig-noheader model/design_smt2.smt2") %
                            (job.workdir, job.opt_depth, engine_idx, engine_idx, engine_idx, engine_idx),
                    logfile=open("%s/engine_%d/logfile2.txt" % (job.workdir, engine_idx), "w"))

            task2_status = None

            def output_callback2(line):
                nonlocal task2_status

                match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
                if match: task2_status = "FAIL"

                match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
                if match: task2_status = "PASS"

            def exit_callback2(line):
                assert task2_status is not None
                assert task2_status == "FAIL"

                job.summary.append("counterexample trace: %s/engine_%d/trace.vcd" % (job.workdir, engine_idx))

            task2.output_callback = output_callback2
            task2.exit_callback = exit_callback2

    task.output_callback = output_callback
    task.exit_callback = exit_callback
    job.engine_tasks.append(task)


def run(job):
    job.opt_depth = 20

    if "depth" in job.options:
        job.opt_depth = int(job.options["depth"])

    job.status = "UNKNOWN"
    job.engine_tasks = list()

    for engine_idx in range(len(job.engines)):
        engine = job.engines[engine_idx]
        assert len(engine) > 0

        job.log("engine_%d: %s" % (engine_idx, " ".join(engine)))
        os.makedirs("%s/engine_%d" % (job.workdir, engine_idx))

        if engine[0] == "smtbmc":
            run_smtbmc(job, engine_idx, engine)

        elif engine[0] == "abc":
            run_abc(job, engine_idx, engine)

        else:
            assert False

    job.taskloop()

