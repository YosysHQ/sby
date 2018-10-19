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
    opts, solver_args = getopt.getopt(engine[1:], "", [])

    if len(solver_args) == 0:
        job.error("Missing solver command.")

    for o, a in opts:
        job.error("Unexpected AIGER engine options.")

    if solver_args[0] == "suprove":
        if mode == "live" and (len(solver_args) == 1 or solver_args[1][0] != "+"):
            solver_args.insert(1, "+simple_liveness")
        solver_cmd = " ".join([job.exe_paths["suprove"]] + solver_args[1:])

    elif solver_args[0] == "avy":
        solver_cmd = " ".join([job.exe_paths["avy"], "--cex", "-"] + solver_args[1:])

    elif solver_args[0] == "aigbmc":
        solver_cmd = " ".join([job.exe_paths["aigbmc"]] + solver_args[1:])

    else:
        job.error("Invalid solver command %s." % solver_args[0])

    task = SbyTask(job, "engine_%d" % engine_idx, job.model("aig"),
            "cd %s; %s model/design_aiger.aig" % (job.workdir, solver_cmd),
            logfile=open("%s/engine_%d/logfile.txt" % (job.workdir, engine_idx), "w"))

    task_status = None
    produced_cex = False
    end_of_cex = False
    aiw_file = open("%s/engine_%d/trace.aiw" % (job.workdir, engine_idx), "w")

    def output_callback(line):
        nonlocal task_status
        nonlocal produced_cex
        nonlocal end_of_cex

        if task_status is not None:
            if not end_of_cex and not produced_cex and line.isdigit():
                produced_cex = True
            if not end_of_cex:
                print(line, file=aiw_file)
            if line == ".":
                end_of_cex = True
            return None

        if line.startswith("u"):
            return "No CEX up to depth %d." % (int(line[1:])-1)

        if line in ["0", "1", "2"]:
            print(line, file=aiw_file)
            if line == "0": task_status = "PASS"
            if line == "1": task_status = "FAIL"
            if line == "2": task_status = "UNKNOWN"

        return None

    def exit_callback(retcode):
        if solver_args[0] not in ["avy"]:
            assert retcode == 0
        assert task_status is not None

        aiw_file.close()

        job.update_status(task_status)
        job.log("engine_%d: Status returned by engine: %s" % (engine_idx, task_status))
        job.summary.append("engine_%d (%s) returned %s" % (engine_idx, " ".join(engine), task_status))

        job.terminate()

        if task_status == "FAIL" and job.opt_aigsmt != "none":
            if produced_cex:
                if mode == "live":
                    task2 = SbyTask(job, "engine_%d" % engine_idx, job.model("smt2"),
                            ("cd %s; %s -g -s %s%s --noprogress -g --dump-vcd engine_%d/trace.vcd --dump-vlogtb engine_%d/trace_tb.v " +
                             "--dump-smtc engine_%d/trace.smtc --aig model/design_aiger.aim:engine_%d/trace.aiw model/design_smt2.smt2") %
                                    (job.workdir, job.exe_paths["smtbmc"], job.opt_aigsmt,
                                    "" if job.opt_tbtop is None else " --vlogtb-top %s" % job.opt_tbtop,
                                    engine_idx, engine_idx, engine_idx, engine_idx),
                            logfile=open("%s/engine_%d/logfile2.txt" % (job.workdir, engine_idx), "w"))
                else:
                    task2 = SbyTask(job, "engine_%d" % engine_idx, job.model("smt2"),
                            ("cd %s; %s -s %s%s --noprogress --append %d -g --dump-vcd engine_%d/trace.vcd --dump-vlogtb engine_%d/trace_tb.v " +
                             "--dump-smtc engine_%d/trace.smtc --aig model/design_aiger.aim:engine_%d/trace.aiw model/design_smt2.smt2") %
                                    (job.workdir, job.exe_paths["smtbmc"], job.opt_aigsmt,
                                    "" if job.opt_tbtop is None else " --vlogtb-top %s" % job.opt_tbtop,
                                    job.opt_append, engine_idx, engine_idx, engine_idx, engine_idx),
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
                    if mode == "live":
                        assert task2_status == "PASS"
                    else:
                        assert task2_status == "FAIL"

                    if os.path.exists("%s/engine_%d/trace.vcd" % (job.workdir, engine_idx)):
                        job.summary.append("counterexample trace: %s/engine_%d/trace.vcd" % (job.workdir, engine_idx))

                task2.output_callback = output_callback2
                task2.exit_callback = exit_callback2

            else:
                job.log("engine_%d: Engine did not produce a counter example." % engine_idx)

    task.output_callback = output_callback
    task.exit_callback = exit_callback

