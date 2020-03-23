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
        job.error("Unexpected BTOR engine options.")

    if solver_args[0] == "btormc":
        solver_cmd = job.exe_paths["btormc"] + " --stop-first -v 1 -kmax {}".format(job.opt_depth - 1)
        if job.opt_skip is not None:
            solver_cmd += " -kmin {}".format(job.opt_skip)
        solver_cmd += " ".join([""] + solver_args[1:])

    else:
        job.error("Invalid solver command {}.".format(solver_args[0]))

    task = SbyTask(job, "engine_{}".format(engine_idx), job.model("btor"),
            "cd {}; {} model/design_btor.btor".format(job.workdir, solver_cmd),
            logfile=open("{}/engine_{}/logfile.txt".format(job.workdir, engine_idx), "w"))

    task_status = None
    produced_cex = False
    end_of_cex = False
    wit_file = open("{}/engine_{}/trace.wit".format(job.workdir, engine_idx), "w")

    def output_callback(line):
        nonlocal task_status
        nonlocal produced_cex
        nonlocal end_of_cex

        if not end_of_cex and not produced_cex and line == "sat":
            produced_cex = True
            task_status = "FAIL"

        if produced_cex and not end_of_cex:
            print(line, file=wit_file)
            if line == ".":
                end_of_cex = True

        if line.startswith("u"):
            return "No CEX up to depth {}.".format(int(line[1:])-1)

        if solver_args[0] == "btormc":
            if "calling BMC on" in line:
                return line
            if "SATISFIABLE" in line:
                return line
            if "bad state properties at bound" in line:
                return line
            if "deleting model checker:" in line:
                if task_status is None:
                    task_status = "PASS"
                return line

        if not produced_cex or end_of_cex:
            print(line, file=task.logfile)

        return None

    def exit_callback(retcode):
        assert retcode == 0
        assert task_status is not None

        if task_status == "PASS":
            print("unsat", file=wit_file)
        wit_file.close()

        job.update_status(task_status)
        job.log("engine_{}: Status returned by engine: {}".format(engine_idx, task_status))
        job.summary.append("engine_{} ({}) returned {}".format(engine_idx, " ".join(engine), task_status))

        job.terminate()

        if task_status == "FAIL" and job.opt_aigsmt != "none":
            if produced_cex:
                has_arrays = False

                with open("{}/model/design_btor.btor".format(job.workdir), "r") as f:
                    for line in f:
                        line = line.split()
                        if len(line) == 5 and line[1] == "sort" and line[2] == "array":
                            has_arrays = True
                            break

                if has_arrays:
                    setupcmd = "cd {};".format(job.workdir)
                    finalwit = "engine_{}/trace.wit".format(engine_idx)
                else:
                    setupcmd = "cd {}; { echo sat; btorsim --states model/design_btor.btor engine_{i}/trace.wit; } > engine_{i}/simtrace.wit &&".format(job.workdir, i=engine_idx)
                    finalwit = "engine_{}/simtrace.wit".format(engine_idx)

                if mode == "live":
                    task2 = SbyTask(job, "engine_{}".format(engine_idx), job.model("smt2"),
                            ("{} {} -g -s {}{} --noprogress --dump-vcd engine_{i}/trace.vcd --dump-vlogtb engine_{i}/trace_tb.v " +
                             "--dump-smtc engine_{i}/trace.smtc --btorwit {} model/design_smt2.smt2").format(setupcmd, job.exe_paths["smtbmc"], job.opt_aigsmt, "" if job.opt_tbtop is None else " --vlogtb-top {}".format(job.opt_tbtop), finalwit, i=engine_idx),
                            logfile=open("{}/engine_{}/logfile2.txt".format(job.workdir, engine_idx), "w"))
                else:
                    task2 = SbyTask(job, "engine_{}".format(engine_idx), job.model("smt2"),
                            ("{} {} -s {}{} --noprogress --append {} --dump-vcd engine_{i}/trace.vcd --dump-vlogtb engine_{i}/trace_tb.v " +
                             "--dump-smtc engine_{i}/trace.smtc --btorwit {} model/design_smt2.smt2").format
                                    (setupcmd, job.exe_paths["smtbmc"], job.opt_aigsmt,
                                     "" if job.opt_tbtop is None else " --vlogtb-top {}".format(job.opt_tbtop),
                                     job.opt_append, finalwit, i=engine_idx),
                            logfile=open("{}/engine_{}/logfile2.txt".format(job.workdir, engine_idx), "w"))

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

                    if os.path.exists("{}/engine_{}/trace.vcd".format(job.workdir, engine_idx)):
                        job.summary.append("counterexample trace: {}/engine_{}/trace.vcd".format(job.workdir, engine_idx))

                task2.output_callback = output_callback2
                task2.exit_callback = exit_callback2

            else:
                job.log("engine_{}: Engine did not produce a counter example.".format(engine_idx))

    task.output_callback = output_callback
    task.exit_callback = exit_callback
