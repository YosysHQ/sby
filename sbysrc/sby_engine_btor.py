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
        solver_cmd = job.exe_paths["btormc"] + " --stop-first {} -v 1 -kmax {}".format(0 if mode == "cover" else 1, job.opt_depth - 1)
        if job.opt_skip is not None:
            solver_cmd += " -kmin {}".format(job.opt_skip)
        solver_cmd += " ".join([""] + solver_args[1:])

    else:
        job.error("Invalid solver command {}.".format(solver_args[0]))

    task = SbyTask(job, "engine_{}".format(engine_idx), job.model("btor"),
            "cd {}; {} model/design_btor.btor".format(job.workdir, solver_cmd),
            logfile=open("{}/engine_{}/logfile.txt".format(job.workdir, engine_idx), "w"))

    solver_status = None
    produced_cex = 0
    expected_cex = 1
    wit_file = None

    def output_callback(line):
        nonlocal solver_status
        nonlocal produced_cex
        nonlocal expected_cex
        nonlocal wit_file

        if mode == "cover":
            match = re.search(r"calling BMC on ([0-9]+) properties", line)
            if match:
                expected_cex = int(match[1])
                assert expected_cex > 0
                assert produced_cex == 0

        if (produced_cex < expected_cex) and line == "sat":
            assert wit_file == None
            if expected_cex == 1:
                wit_file = open("{}/engine_{}/trace.wit".format(job.workdir, engine_idx), "w")
            else:
                wit_file = open("{}/engine_{}/trace{}.wit".format(job.workdir, engine_idx, produced_cex), "w")

        if wit_file:
            print(line, file=wit_file)
            if line == ".":
                produced_cex += 1
                wit_file.close()
                wit_file = None
                if produced_cex == expected_cex:
                    solver_status = "sat"

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
                if solver_status is None:
                    solver_status = "unsat"
                return line

        if not wit_file:
            print(line, file=task.logfile)

        return None

    def exit_callback(retcode):
        assert retcode == 0
        assert solver_status is not None

        if solver_status == "unsat":
            if expected_cex == 1:
                with open("{}/engine_{}/trace.wit".format(job.workdir, engine_idx), "w") as wit_file:
                    print("unsat", file=wit_file)
            else:
                for i in range(produced_cex, expected_cex):
                    with open("{}/engine_{}/trace{}.wit".format(job.workdir, engine_idx, i), "w") as wit_file:
                        print("unsat", file=wit_file)

        if mode == "cover":
            task_status = "PASS" if solver_status == "sat" else "FAIL"
        else:
            task_status = "FAIL" if solver_status == "sat" else "PASS"

        job.update_status(task_status)
        job.log("engine_{}: Status returned by engine: {}".format(engine_idx, task_status))
        job.summary.append("engine_{} ({}) returned {}".format(engine_idx, " ".join(engine), task_status))

        job.terminate()

        if produced_cex == 0:
            job.log("engine_{}: Engine did not produce a counter example.".format(engine_idx))
        elif produced_cex == 1:
            task2 = SbyTask(job, "engine_{}".format(engine_idx), job.model("btor"),
                    "cd {dir}; btorsim -c --vcd engine_{idx}/trace.vcd --hierarchical-symbols model/design_btor.btor engine_{idx}/trace.wit".format(dir=job.workdir, idx=engine_idx),
                    logfile=open("{dir}/engine_{idx}/logfile2.txt".format(dir=job.workdir, idx=engine_idx), "w"))

            def output_callback2(line):
                return line

            def exit_callback2(line):
                assert retcode == 0

                if os.path.exists("{}/engine_{}/trace.vcd".format(job.workdir, engine_idx)):
                    job.summary.append("counterexample trace: {}/engine_{}/trace.vcd".format(job.workdir, engine_idx))

            task2.output_callback = output_callback2
            task2.exit_callback = exit_callback2

        else:
            def output_callback2(line):
                return line

            def make_exit_callback2(i):
                def exit_callback2(line):
                    assert retcode == 0

                    if os.path.exists("{}/engine_{}/trace{}.vcd".format(job.workdir, engine_idx, i)):
                        job.summary.append("counterexample trace: {}/engine_{}/trace{}.vcd".format(job.workdir, engine_idx, i))
                return exit_callback2

            for i in range(produced_cex):
                task2 = SbyTask(job, "engine_{}".format(engine_idx), job.model("btor"),
                        "cd {dir}; btorsim -c --vcd engine_{idx}/trace{i}.vcd --hierarchical-symbols model/design_btor.btor engine_{idx}/trace{i}.wit".format(dir=job.workdir, idx=engine_idx, i=i),
                        logfile=open("{dir}/engine_{idx}/logfile{}.txt".format(i+2, dir=job.workdir, idx=engine_idx), "w"))

                task2.output_callback = output_callback2
                task2.exit_callback = make_exit_callback2(i)

    task.output_callback = output_callback
    task.exit_callback = exit_callback
