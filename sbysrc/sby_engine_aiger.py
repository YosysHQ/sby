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

import re, os, getopt
from sby_core import SbyProc

def run(mode, task, engine_idx, engine):
    opts, solver_args = getopt.getopt(engine[1:], "", [])

    if len(solver_args) == 0:
        task.error("Missing solver command.")

    for o, a in opts:
        task.error("Unexpected AIGER engine options.")

    status_2 = "UNKNOWN"

    if solver_args[0] == "suprove":
        if mode not in ["live", "prove"]:
            task.error("The aiger solver 'suprove' is only supported in live and prove modes.")
        if mode == "live" and (len(solver_args) == 1 or solver_args[1][0] != "+"):
            solver_args.insert(1, "+simple_liveness")
        solver_cmd = " ".join([task.exe_paths["suprove"]] + solver_args[1:])

    elif solver_args[0] == "avy":
        if mode != "prove":
            task.error("The aiger solver 'avy' is only supported in prove mode.")
        solver_cmd = " ".join([task.exe_paths["avy"], "--cex", "-"] + solver_args[1:])

    elif solver_args[0] == "aigbmc":
        if mode != "bmc":
            task.error("The aiger solver 'aigbmc' is only supported in bmc mode.")
        solver_cmd = " ".join([task.exe_paths["aigbmc"], str(task.opt_depth - 1)] + solver_args[1:])
        status_2 = "PASS"  # aigbmc outputs status 2 when BMC passes

    else:
        task.error(f"Invalid solver command {solver_args[0]}.")

    proc = SbyProc(
        task,
        f"engine_{engine_idx}",
        task.model("aig"),
        f"cd {task.workdir}; {solver_cmd} model/design_aiger.aig",
        logfile=open(f"{task.workdir}/engine_{engine_idx}/logfile.txt", "w")
    )
    if solver_args[0] not in ["avy"]:
        proc.checkretcode = True

    proc_status = None
    produced_cex = False
    end_of_cex = False
    aiw_file = open(f"{task.workdir}/engine_{engine_idx}/trace.aiw", "w")

    def output_callback(line):
        nonlocal proc_status
        nonlocal produced_cex
        nonlocal end_of_cex

        if proc_status is not None:
            if not end_of_cex and not produced_cex and line.isdigit():
                produced_cex = True
            if not end_of_cex:
                print(line, file=aiw_file)
            if line == ".":
                end_of_cex = True
            return None

        if line.startswith("u"):
            return f"No CEX up to depth {int(line[1:])-1}."

        if line in ["0", "1", "2"]:
            print(line, file=aiw_file)
            if line == "0": proc_status = "PASS"
            if line == "1": proc_status = "FAIL"
            if line == "2": proc_status = status_2

        return None

    def exit_callback(retcode):
        if proc_status is None:
            task.error(f"engine_{engine_idx}: Could not determine engine status.")

        aiw_file.close()

        task.update_status(proc_status)
        task.log(f"engine_{engine_idx}: Status returned by engine: {proc_status}")
        task.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {proc_status}""")

        task.terminate()

        if proc_status == "FAIL" and task.opt_aigsmt != "none":
            if produced_cex:
                if mode == "live":
                    proc2 = SbyProc(
                        task,
                        f"engine_{engine_idx}",
                        task.model("smt2"),
                        ("cd {}; {} -g -s {}{} --noprogress --dump-vcd engine_{i}/trace.vcd --dump-vlogtb engine_{i}/trace_tb.v " +
                             "--dump-smtc engine_{i}/trace.smtc --aig model/design_aiger.aim:engine_{i}/trace.aiw model/design_smt2.smt2").format
                                    (task.workdir, task.exe_paths["smtbmc"], task.opt_aigsmt,
                                    "" if task.opt_tbtop is None else f" --vlogtb-top {task.opt_tbtop}",
                                    i=engine_idx),
                        logfile=open(f"{task.workdir}/engine_{engine_idx}/logfile2.txt", "w")
                    )
                else:
                    proc2 = SbyProc(
                        task,
                        f"engine_{engine_idx}",
                        task.model("smt2"),
                        ("cd {}; {} -s {}{} --noprogress --append {} --dump-vcd engine_{i}/trace.vcd --dump-vlogtb engine_{i}/trace_tb.v " +
                             "--dump-smtc engine_{i}/trace.smtc --aig model/design_aiger.aim:engine_{i}/trace.aiw model/design_smt2.smt2").format
                                    (task.workdir, task.exe_paths["smtbmc"], task.opt_aigsmt,
                                    "" if task.opt_tbtop is None else f" --vlogtb-top {task.opt_tbtop}",
                                    task.opt_append, i=engine_idx),
                        logfile=open(f"{task.workdir}/engine_{engine_idx}/logfile2.txt", "w")
                    )

                proc2_status = None

                def output_callback2(line):
                    nonlocal proc2_status

                    match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
                    if match: proc2_status = "FAIL"

                    match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
                    if match: proc2_status = "PASS"

                    return line

                def exit_callback2(line):
                    if proc2_status is None:
                        task.error(f"engine_{engine_idx}: Could not determine aigsmt status.")
                    if proc2_status != ("PASS" if mode == "live" else "FAIL"):
                        task.error(f"engine_{engine_idx}: Unexpected aigsmt status.")

                    if os.path.exists(f"{task.workdir}/engine_{engine_idx}/trace.vcd"):
                        task.summary.append(f"counterexample trace: {task.workdir}/engine_{engine_idx}/trace.vcd")

                proc2.output_callback = output_callback2
                proc2.exit_callback = exit_callback2

            else:
                task.log(f"engine_{engine_idx}: Engine did not produce a counter example.")

    proc.output_callback = output_callback
    proc.exit_callback = exit_callback
