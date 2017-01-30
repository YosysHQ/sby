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
    if mode == "bmc":
        assert engine == ["abc", "bmc3"]
        abc_command = "bmc3 -F %d -v" % job.opt_depth

    elif mode == "prove":
        assert engine == ["abc", "pdr"]
        abc_command = "pdr"

    else:
        assert False

    task = SbyTask(job, "engine_%d" % engine_idx, job.model("aig"),
            ("cd %s; yosys-abc -c 'read_aiger model/design_aiger.aig; fold; strash; %s; " +
             "write_cex -a engine_%d/trace.aiw'") % (job.workdir, abc_command, engine_idx),
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

        match = re.match(r"^Property proved.", line)
        if match: task_status = "PASS"

    def exit_callback(retcode):
        assert retcode == 0
        assert task_status is not None

        job.status = task_status
        job.log("engine_%d: Status returned by engine: %s" % (engine_idx, task_status))
        job.summary.append("engine_%d (%s) returned %s" % (engine_idx, " ".join(engine), job.status))

        job.terminate()

        if job.status == "FAIL":
            task2 = SbyTask(job, "engine_%d" % engine_idx, job.model("smt2"),
                    ("cd %s; yosys-smtbmc --noprogress --dump-vcd engine_%d/trace.vcd --dump-vlogtb engine_%d/trace_tb.v " +
                     "--dump-smtc engine_%d/trace.smtc --aig model/design_aiger.aim:engine_%d/trace.aiw --aig-noheader model/design_smt2.smt2") %
                            (job.workdir, engine_idx, engine_idx, engine_idx, engine_idx),
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

