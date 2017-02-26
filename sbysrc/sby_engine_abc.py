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
    abc_opts, abc_command = getopt.getopt(engine[1:], "", [])
    assert len(abc_command) > 0

    for o, a in abc_opts:
        assert False

    if abc_command[0] == "bmc3":
        assert mode == "bmc"
        assert len(abc_command) == 1
        abc_command[0] += " -F %d -v" % job.opt_depth

    elif abc_command[0] == "sim3":
        assert mode == "bmc"
        abc_command[0] += " -F %d -v" % job.opt_depth

    elif abc_command[0] == "pdr":
        assert mode == "prove"

    else:
        assert False

    task = SbyTask(job, "engine_%d" % engine_idx, job.model("aig"),
            ("cd %s; %s -c 'read_aiger model/design_aiger.aig; fold; strash; %s; write_cex -a engine_%d/trace.aiw'") %
            (job.workdir, job.exe_paths["abc"], " ".join(abc_command), engine_idx),
            logfile=open("%s/engine_%d/logfile.txt" % (job.workdir, engine_idx), "w"))

    task.noprintregex = re.compile(r"^\.+$")
    task_status = None

    def output_callback(line):
        nonlocal task_status

        match = re.match(r"^Output [0-9]+ of miter .* was asserted in frame [0-9]+.", line)
        if match: task_status = "FAIL"

        match = re.match(r"^Simulation of [0-9]+ frames for [0-9]+ rounds with [0-9]+ restarts did not assert POs.", line)
        if match: task_status = "UNKNOWN"

        match = re.match(r"^Stopping BMC because all 2\^[0-9]+ reachable states are visited.", line)
        if match: task_status = "PASS"

        match = re.match(r"^No output asserted in [0-9]+ frames.", line)
        if match: task_status = "PASS"

        match = re.match(r"^Property proved.", line)
        if match: task_status = "PASS"

        return line

    def exit_callback(retcode):
        assert retcode == 0
        assert task_status is not None

        job.update_status(task_status)
        job.log("engine_%d: Status returned by engine: %s" % (engine_idx, task_status))
        job.summary.append("engine_%d (%s) returned %s" % (engine_idx, " ".join(engine), task_status))

        job.terminate()

        if task_status == "FAIL":
            task2 = SbyTask(job, "engine_%d" % engine_idx, job.model("smt2"),
                    ("cd %s; %s -s %s --noprogress --append %d --dump-vcd engine_%d/trace.vcd --dump-vlogtb engine_%d/trace_tb.v " +
                     "--dump-smtc engine_%d/trace.smtc --aig model/design_aiger.aim:engine_%d/trace.aiw --aig-noheader model/design_smt2.smt2") %
                            (job.workdir, job.exe_paths["smtbmc"], job.opt_aigsmt, job.opt_append, engine_idx, engine_idx, engine_idx, engine_idx),
                    logfile=open("%s/engine_%d/logfile2.txt" % (job.workdir, engine_idx), "w"))

            task2_status = None

            def output_callback2(line):
                nonlocal task2_status

                match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
                if match: task2_status = "FAIL"

                match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
                if match: task2_status = "PASS"

                return line

            def exit_callback2(line):
                assert task2_status is not None
                assert task2_status == "FAIL"

                job.summary.append("counterexample trace: %s/engine_%d/trace.vcd" % (job.workdir, engine_idx))

            task2.output_callback = output_callback2
            task2.exit_callback = exit_callback2

    task.output_callback = output_callback
    task.exit_callback = exit_callback

