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

    if len(abc_command) == 0:
        job.error("Missing ABC command.")

    for o, a in abc_opts:
        job.error("Unexpected ABC engine options.")

    if abc_command[0] == "bmc3":
        if mode != "bmc":
            job.error("ABC command 'bmc3' is only valid in bmc mode.")
        abc_command[0] += f" -F {job.opt_depth} -v"

    elif abc_command[0] == "sim3":
        if mode != "bmc":
            job.error("ABC command 'sim3' is only valid in bmc mode.")
        abc_command[0] += f" -F {job.opt_depth} -v"

    elif abc_command[0] == "pdr":
        if mode != "prove":
            job.error("ABC command 'pdr' is only valid in prove mode.")

    else:
        job.error(f"Invalid ABC command {abc_command[0]}.")

    task = SbyTask(
        job,
        f"engine_{engine_idx}",
        job.model("aig"),
        f"""cd {job.workdir}; {job.exe_paths["abc"]} -c 'read_aiger model/design_aiger.aig; fold; strash; {" ".join(abc_command)}; write_cex -a engine_{engine_idx}/trace.aiw'""",
        logfile=open(f"{job.workdir}/engine_{engine_idx}/logfile.txt", "w")
    )

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
        job.log(f"engine_{engine_idx}: Status returned by engine: {task_status}")
        job.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {task_status}""")

        job.terminate()

        if task_status == "FAIL" and job.opt_aigsmt != "none":
            task2 = SbyTask(
                job,
                f"engine_{engine_idx}",
                job.model("smt2"),
                ("cd {}; {} -s {}{} --noprogress --append {} --dump-vcd engine_{i}/trace.vcd --dump-vlogtb engine_{i}/trace_tb.v " +
                     "--dump-smtc engine_{i}/trace.smtc --aig model/design_aiger.aim:engine_{i}/trace.aiw --aig-noheader model/design_smt2.smt2").format
                            (job.workdir, job.exe_paths["smtbmc"], job.opt_aigsmt,
                            "" if job.opt_tbtop is None else f" --vlogtb-top {job.opt_tbtop}",
                            job.opt_append, i=engine_idx),
                logfile=open(f"{job.workdir}/engine_{engine_idx}/logfile2.txt", "w")
            )

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

                if os.path.exists(f"{job.workdir}/engine_{engine_idx}/trace.vcd"):
                    job.summary.append(f"counterexample trace: {job.workdir}/engine_{engine_idx}/trace.vcd")

            task2.output_callback = output_callback2
            task2.exit_callback = exit_callback2

    task.output_callback = output_callback
    task.exit_callback = exit_callback
