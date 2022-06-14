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
    abc_opts, abc_command = getopt.getopt(engine[1:], "", [])

    if len(abc_command) == 0:
        task.error("Missing ABC command.")

    for o, a in abc_opts:
        task.error("Unexpected ABC engine options.")

    if abc_command[0] == "bmc3":
        if mode != "bmc":
            task.error("ABC command 'bmc3' is only valid in bmc mode.")
        abc_command[0] += f" -F {task.opt_depth} -v"

    elif abc_command[0] == "sim3":
        if mode != "bmc":
            task.error("ABC command 'sim3' is only valid in bmc mode.")
        abc_command[0] += f" -F {task.opt_depth} -v"

    elif abc_command[0] == "pdr":
        if mode != "prove":
            task.error("ABC command 'pdr' is only valid in prove mode.")

    else:
        task.error(f"Invalid ABC command {abc_command[0]}.")

    proc = SbyProc(
        task,
        f"engine_{engine_idx}",
        task.model("aig"),
        f"""cd {task.workdir}; {task.exe_paths["abc"]} -c 'read_aiger model/design_aiger.aig; fold; strash; {" ".join(abc_command)}; write_cex -a engine_{engine_idx}/trace.aiw'""",
        logfile=open(f"{task.workdir}/engine_{engine_idx}/logfile.txt", "w")
    )
    proc.checkretcode = True

    proc.noprintregex = re.compile(r"^\.+$")
    proc_status = None

    def output_callback(line):
        nonlocal proc_status

        match = re.match(r"^Output [0-9]+ of miter .* was asserted in frame [0-9]+.", line)
        if match: proc_status = "FAIL"

        match = re.match(r"^Simulation of [0-9]+ frames for [0-9]+ rounds with [0-9]+ restarts did not assert POs.", line)
        if match: proc_status = "UNKNOWN"

        match = re.match(r"^Stopping BMC because all 2\^[0-9]+ reachable states are visited.", line)
        if match: proc_status = "PASS"

        match = re.match(r"^No output asserted in [0-9]+ frames.", line)
        if match: proc_status = "PASS"

        match = re.match(r"^Property proved.", line)
        if match: proc_status = "PASS"

        return line

    def exit_callback(retcode):
        if proc_status is None:
            task.error(f"engine_{engine_idx}: Could not determine engine status.")

        task.update_status(proc_status)
        task.log(f"engine_{engine_idx}: Status returned by engine: {proc_status}")
        task.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {proc_status}""")

        task.terminate()

        if proc_status == "FAIL" and task.opt_aigsmt != "none":
            proc2 = SbyProc(
                task,
                f"engine_{engine_idx}",
                task.model("smt2"),
                ("cd {}; {} -s {}{} --noprogress --append {} --dump-vcd engine_{i}/trace.vcd --dump-vlogtb engine_{i}/trace_tb.v " +
                     "--dump-smtc engine_{i}/trace.smtc --aig model/design_aiger.aim:engine_{i}/trace.aiw --aig-noheader model/design_smt2.smt2").format
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

            def exit_callback2(retcode):
                if proc2_status is None:
                    task.error(f"engine_{engine_idx}: Could not determine aigsmt status.")
                if proc2_status != "FAIL":
                    task.error(f"engine_{engine_idx}: Unexpected aigsmt status.")

                if os.path.exists(f"{task.workdir}/engine_{engine_idx}/trace.vcd"):
                    task.summary.append(f"counterexample trace: {task.workdir}/engine_{engine_idx}/trace.vcd")

            proc2.output_callback = output_callback2
            proc2.exit_callback = exit_callback2

    proc.output_callback = output_callback
    proc.exit_callback = exit_callback
